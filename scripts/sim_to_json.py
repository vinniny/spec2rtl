#!/usr/bin/env python3
"""Convert simulation log to structured JSON and emit a run manifest."""
from __future__ import annotations

import argparse
import json
import pathlib
import platform
import re
import subprocess
from datetime import datetime, timezone
from hashlib import sha1
from typing import Any, Dict

from json_schemas import SchemaError, validate_sim_report


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Convert simulation log to JSON")
    parser.add_argument("--log", type=pathlib.Path, required=True)
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/sim_report.json"))
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports"))
    parser.add_argument("--duration", type=float, default=None)
    parser.add_argument("--seed", type=int, default=None)
    parser.add_argument("--manifest", type=pathlib.Path, default=pathlib.Path("reports/run_manifest.json"))
    parser.add_argument("--flaky-attempts", type=int, default=0)
    parser.add_argument("--max-attempts", type=int, default=0)
    return parser.parse_args()


def read_log(log_path: pathlib.Path) -> str:
    if not log_path.exists():
        raise SystemExit(f"Log file {log_path} not found")
    return log_path.read_text(encoding="utf-8", errors="ignore")


def parse_log(text: str) -> tuple[Dict[str, Any], str]:
    failures = []
    pass_count = 0
    coverage_samples: dict[str, int] = {}
    seed = None

    seed_match = re.search(r"\[META\]\s+SEED=(\d+)", text)
    if seed_match:
        seed = int(seed_match.group(1))

    for line in text.splitlines():
        mismatch = re.search(r"\[(R[-A-Z0-9]+)\]\s+Mismatch: a=(\d+) b=(\d+) got=(\d+) exp=(\d+)", line)
        if mismatch:
            rid, a, b, got, exp = mismatch.groups()
            failures.append(
                {
                    "req": rid,
                    "a": int(a),
                    "b": int(b),
                    "got": int(got),
                    "exp": int(exp),
                    "line": line.strip(),
                }
            )
        if re.search(r"\[(R[-A-Z0-9]+)\]\s+PASS", line):
            pass_count += 1
        sample = re.search(r"\[COV\]\s+(R[-A-Z0-9]+)", line)
        if sample:
            rid = sample.group(1)
            coverage_samples[rid] = coverage_samples.get(rid, 0) + 1

    summary = {
        "schema": 1,
        "status": "fail" if failures else "pass",
        "pass_count": pass_count,
        "fail_count": len(failures),
        "failures": failures,
        "coverage_samples": coverage_samples,
    }
    if seed is not None:
        summary["seed"] = seed
    return summary, sha1(text.encode("utf-8")).hexdigest()[:12]


def load_env_versions(reports_dir: pathlib.Path) -> Dict[str, Any]:
    env_path = reports_dir / "env.json"
    if not env_path.exists():
        return {}
    try:
        return json.loads(env_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def git_info() -> Dict[str, Any]:
    def capture(cmd: str) -> str:
        try:
            result = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.STDOUT)
        except Exception:
            return "n/a"
        return result.strip()

    sha = capture("git rev-parse HEAD")
    status = capture("git status --porcelain")
    dirty = status not in {"", "n/a"}
    return {"sha": sha, "dirty": dirty}


def write_manifest(
    manifest_path: pathlib.Path,
    reports_dir: pathlib.Path,
    seed: int | None,
    signature: str,
    duration: float | None,
) -> None:
    manifest = {
        "schema": 1,
        "timestamp_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "host": platform.node(),
        "git": git_info(),
        "tools": load_env_versions(reports_dir).get("tools", {}),
        "python": platform.python_version(),
        "simulation": {
            "signature": signature,
        },
    }
    if seed is not None:
        manifest["seed"] = seed
    if duration is not None:
        manifest["simulation"]["runtime_seconds"] = duration

    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"Wrote {manifest_path}")


def main() -> None:
    args = parse_args()
    log_text = read_log(args.log)
    sim_summary, signature = parse_log(log_text)

    if args.duration is not None:
        sim_summary["runtime_seconds"] = args.duration
    if args.seed is not None:
        sim_summary["seed"] = args.seed

    reports_dir = args.reports
    reports_dir.mkdir(parents=True, exist_ok=True)

    coverage_info = reports_dir / "coverage.info"
    if coverage_info.exists():
        sim_summary["coverage"] = {"info_path": str(coverage_info)}

    out_path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    total_tests = sim_summary.get("pass_count", 0) + sim_summary.get("fail_count", 0)
    if total_tests == 0:
        print("[sim] ERROR: No simulation tests executed; refusing to emit empty report")
        raise SystemExit(2)
    if args.flaky_attempts:
        sim_summary["flaky"] = {
            "retries": int(args.flaky_attempts),
            "max_attempts": max(int(args.max_attempts), int(args.flaky_attempts) + 1),
        }
    try:
        validate_sim_report(sim_summary)
    except SchemaError as exc:
        raise SystemExit(f"sim_report schema validation failed: {exc}") from exc

    out_path.write_text(json.dumps(sim_summary, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")

    write_manifest(args.manifest, reports_dir, sim_summary.get("seed"), signature, args.duration)


if __name__ == "__main__":
    main()
