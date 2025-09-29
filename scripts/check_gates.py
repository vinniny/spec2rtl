#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import pathlib
import sys

from typing import Any

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

SIM_REPORT = pathlib.Path("reports/sim_report.json")
COVERAGE_JSON = pathlib.Path("reports/coverage.json")
COVERAGE_PER_REQ = pathlib.Path("reports/coverage_per_req.json")
REQS_YML = pathlib.Path("verification/reqs.yml")


def get_nested_count(counts: dict[str, Any], path: str) -> int | None:
    value: Any = counts
    for part in path.split('.'):
        if not isinstance(value, dict):
            return None
        value = value.get(part)
        if value is None:
            return None
    return value if isinstance(value, int) else None

if not SIM_REPORT.exists():
    raise SystemExit("Missing sim_report.json. Run make report first")

sim = json.loads(SIM_REPORT.read_text(encoding="utf-8"))
if sim.get("status") != "pass":
    print("Sim failed")
    sys.exit(1)

coverage = json.loads(COVERAGE_JSON.read_text(encoding="utf-8")) if COVERAGE_JSON.exists() else {}
per_req = json.loads(COVERAGE_PER_REQ.read_text(encoding="utf-8")) if COVERAGE_PER_REQ.exists() else {"requirements": []}
reqs = yaml.safe_load(REQS_YML.read_text(encoding="utf-8")) if REQS_YML.exists() else {"requirements": []}

line_cov = coverage.get("line")
toggle_cov = coverage.get("toggle")
line_min = float(os.environ.get("LINE_COV_MIN", "0"))
toggle_min = float(os.environ.get("TOGGLE_COV_MIN", "0"))

if line_cov is not None and line_cov < line_min:
    print(f"Line coverage below global threshold: {line_cov:.4f} < {line_min}")
    sys.exit(1)
if toggle_cov is not None and toggle_cov < toggle_min:
    print(f"Toggle coverage below global threshold: {toggle_cov:.4f} < {toggle_min}")
    sys.exit(1)

per_req_map = {entry.get("id"): entry for entry in per_req.get("requirements", [])}

for req in reqs.get("requirements", []):
    rid = req.get("id")
    targets = req.get("cov_targets", {}) or {}
    line_target = targets.get("line")
    toggle_target = targets.get("toggle")
    summary = per_req_map.get(rid, {})
    line_val = summary.get("line", 0.0)
    toggle_val = summary.get("toggle", 0.0)
    if line_target is not None and line_val < line_target:
        print(f"Requirement {rid} line coverage below threshold: {line_val:.4f} < {line_target}")
        sys.exit(1)
    if toggle_target is not None and toggle_val < toggle_target:
        print(f"Requirement {rid} toggle coverage below threshold: {toggle_val:.4f} < {toggle_target}")
        sys.exit(1)

    bin_targets = targets.get("bins") if isinstance(targets, dict) else None
    if isinstance(bin_targets, dict):
        bins_summary = summary.get("bins", {}) if isinstance(summary, dict) else {}
        bin_counts = bins_summary.get("counts", {}) if isinstance(bins_summary, dict) else {}
        bin_coverage = bins_summary.get("coverage", {}) if isinstance(bins_summary, dict) else {}
        for bin_name, threshold in bin_targets.items():
            if isinstance(threshold, (int, float)):
                value = bin_coverage.get(bin_name)
                if value is None:
                    print(f"Requirement {rid} missing coverage metric for bin '{bin_name}'")
                    sys.exit(1)
                if value < float(threshold):
                    print(f"Requirement {rid} bin '{bin_name}' coverage below threshold: {value:.4f} < {threshold}")
                    sys.exit(1)
            elif isinstance(threshold, list):
                for required_bin in threshold:
                    count = get_nested_count(bin_counts, required_bin)
                    if count is None or count <= 0:
                        print(f"Requirement {rid} missing required bin hit '{required_bin}'")
                        sys.exit(1)
            else:
                print(f"Requirement {rid} has unsupported bin target type for '{bin_name}'")
                sys.exit(1)

print("Coverage gates passed")
