#!/usr/bin/env python3
"""Wrapper that runs the simulation binary with retry support and JSON emission."""
from __future__ import annotations

import argparse
import os
import shlex
import subprocess
import sys
import time
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Execute simulation with retries and emit JSON reports")
    parser.add_argument("--sim-bin", required=True)
    parser.add_argument("--sim-args", default="")
    parser.add_argument("--log", type=Path, required=True)
    parser.add_argument("--reports", type=Path, required=True)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--flaky-retries", type=int, default=0)
    parser.add_argument("--python", default=sys.executable)
    return parser.parse_args()


def main() -> int:
    args = parse_args()

    reports_dir = args.reports
    reports_dir.mkdir(parents=True, exist_ok=True)
    log_path = args.log
    if log_path.exists():
        log_path.unlink()

    cmd = [args.sim_bin]
    if args.sim_args:
        cmd.extend(shlex.split(args.sim_args))

    last_status = 0
    duration = 0.0
    attempts_used = 0

    env = dict(os.environ)
    env["REPORTS_DIR"] = str(reports_dir)

    for attempt in range(args.flaky_retries + 1):
        attempts_used = attempt
        start = time.time()
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, env=env)
        duration = time.time() - start
        with log_path.open("a", encoding="utf-8") as log:
            log.write(f"\n--- attempt {attempt} ---\n")
            log.write(proc.stdout)
        last_status = proc.returncode
        if last_status == 0:
            break

    flaky_attempts = attempts_used if last_status == 0 else args.flaky_retries + 1

    sim_report = reports_dir / "sim_report.json"
    manifest = args.manifest

    json_cmd = [
        args.python,
        "scripts/sim_to_json.py",
        "--log",
        str(log_path),
        "--out",
        str(sim_report),
        "--reports",
        str(reports_dir),
        "--duration",
        f"{duration}",
        "--seed",
        str(args.seed),
        "--manifest",
        str(manifest),
        "--flaky-attempts",
        str(flaky_attempts if flaky_attempts > 0 and last_status == 0 else 0),
        "--max-attempts",
        str(args.flaky_retries + 1),
    ]

    result = subprocess.run(json_cmd)
    if result.returncode != 0:
        return result.returncode

    return last_status


if __name__ == "__main__":
    sys.exit(main())
