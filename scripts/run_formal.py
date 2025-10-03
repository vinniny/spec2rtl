#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
from typing import Any, Dict, List

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

from json_schemas import SchemaError, validate_formal_summary


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run SymbiYosys tasks from profile files")
    parser.add_argument("--profiles", type=pathlib.Path, nargs="+", required=True, help="YAML profile files")
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/formal"))
    parser.add_argument("--sby", type=str, default=os.environ.get("SBY", "sby"))
    parser.add_argument("--base", type=pathlib.Path, help="Base directory for relative SBY paths")
    return parser.parse_args()


def load_profile(path: pathlib.Path, base_dir: pathlib.Path | None = None) -> List[Dict[str, Any]]:
    if not path.exists():
        raise SystemExit(f"Formal profile not found: {path}")
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise SystemExit(f"Failed to parse profile {path}: {exc}") from exc
    tasks = data.get("tasks", [])
    if not isinstance(tasks, list):
        raise SystemExit(f"Profile {path} must define a list of tasks")
    normalized: List[Dict[str, Any]] = []
    if base_dir is None:
        base_dir = pathlib.Path(__file__).resolve().parents[1]
    for entry in tasks:
        if isinstance(entry, str):
            entry_map: Dict[str, Any] = {"sby": entry}
        elif isinstance(entry, dict):
            entry_map = entry
        else:
            raise SystemExit(f"Task entry in {path} must be a mapping or string")
        sby_path = entry_map.get("sby") or entry_map.get("path")
        if not isinstance(sby_path, str):
            raise SystemExit(f"Task in {path} is missing 'sby' path")
        name = entry_map.get("name")
        if not isinstance(name, str) or not name:
            name = pathlib.Path(sby_path).stem
        sby_file = pathlib.Path(sby_path)
        if not sby_file.is_absolute():
            sby_file = (base_dir / sby_file).resolve()
        normalized.append(
            {
                "name": name,
                "sby": sby_file,
                "optional": bool(entry_map.get("optional", False)),
            }
        )
    return normalized


def run_task(sby_bin: str, task: Dict[str, Any], out_dir: pathlib.Path) -> Dict[str, Any]:
    sby_path: pathlib.Path = task["sby"].resolve()
    if not sby_path.exists():
        raise SystemExit(f"SBY file not found: {sby_path}")

    task_dir = out_dir / task["name"]
    task_dir.parent.mkdir(parents=True, exist_ok=True)
    if task_dir.exists():
        shutil.rmtree(task_dir)
    task_dir.mkdir(parents=True, exist_ok=True)

    log_path = task_dir / "run.log"
    cmd = [sby_bin, "-f", str(sby_path), "-d", str(task_dir)]
    with log_path.open("w", encoding="utf-8") as log_file:
        result = subprocess.run(cmd, stdout=log_file, stderr=subprocess.STDOUT, check=False)
    sby_log = task_dir / "logfile.txt"
    if sby_log.exists():
        shutil.copy2(sby_log, log_path)
    status = "PASS" if result.returncode == 0 else "FAIL"

    summary = {
        "name": task["name"],
        "sby": str(sby_path),
        "status": status,
        "return_code": result.returncode,
        "log": str(log_path),
        "optional": task.get("optional", False),
    }

    status_file = task_dir / "status"
    if status_file.exists():
        summary["status_file"] = status_file.read_text(encoding="utf-8").strip()

    return summary


def main() -> None:
    args = parse_args()
    out_dir = args.out
    out_dir.mkdir(parents=True, exist_ok=True)

    base_dir = args.base.resolve() if args.base else None
    tasks: List[Dict[str, Any]] = []
    for profile in args.profiles:
        tasks.extend(load_profile(profile, base_dir))

    results: List[Dict[str, Any]] = []
    hard_failure = False

    for task in tasks:
        summary = run_task(args.sby, task, out_dir)
        results.append(summary)
        if summary["status"] != "PASS" and not summary.get("optional", False):
            hard_failure = True
            log_path = pathlib.Path(summary.get("log", ""))
            if log_path.exists():
                log_lines = log_path.read_text(encoding="utf-8", errors="ignore").splitlines()
                tail = "\n".join(log_lines[-20:])
                print("[formal] tail of", log_path)
                print(tail)

    summary_path = out_dir / "summary.json"
    payload = {
        "schema": 1,
        "tasks": results,
    }
    try:
        validate_formal_summary(payload)
    except SchemaError as exc:
        raise SystemExit(f"formal summary schema validation failed: {exc}") from exc

    summary_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {summary_path}")

    if hard_failure:
        raise SystemExit("Formal checks failed")


if __name__ == "__main__":
    main()
