#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import re
import sys
from hashlib import sha1

if len(sys.argv) not in (2, 3):
    raise SystemExit("usage: sim_to_json.py <sim.log> [duration_seconds]")

log_path = pathlib.Path(sys.argv[1])
duration = float(sys.argv[2]) if len(sys.argv) == 3 else None
if not log_path.exists():
    raise SystemExit(f"Log file {log_path} not found")

text = log_path.read_text(encoding="utf-8", errors="ignore")

seed = None
seed_match = re.search(r"\[META\]\s+SEED=(\d+)", text)
if seed_match:
    seed = int(seed_match.group(1))

failures = []
pass_count = 0
coverage_samples: dict[str, int] = {}
for line in text.splitlines():
    mismatch = re.search(r"\[(R\d+)\]\s+Mismatch: a=(\d+) b=(\d+) got=(\d+) exp=(\d+)", line)
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
    if re.search(r"\[(R\d+)\]\s+PASS", line):
        pass_count += 1
    sample = re.search(r"\[COV\]\s+(R\d+)", line)
    if sample:
        rid = sample.group(1)
        coverage_samples[rid] = coverage_samples.get(rid, 0) + 1

signature = sha1(text.encode("utf-8")).hexdigest()[:12]

out = {
    "schema": 1,
    "status": "fail" if failures else "pass",
    "pass_count": pass_count,
    "fail_count": len(failures),
    "failures": failures,
    "seed": seed,
    "signature": signature,
    "coverage_samples": coverage_samples,
}

if duration is not None:
    out["runtime_seconds"] = duration

coverage_info = pathlib.Path("reports/coverage.info")
if coverage_info.exists():
    out["coverage"] = {"info_path": str(coverage_info)}

reports_dir = pathlib.Path("reports")
reports_dir.mkdir(parents=True, exist_ok=True)
report_path = reports_dir / "sim_report.json"
report_path.write_text(json.dumps(out, indent=2), encoding="utf-8")
print(f"Wrote {report_path}")
