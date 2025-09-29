#!/usr/bin/env python3
from __future__ import annotations

import csv
import json
import pathlib
from typing import Dict, List

REQ_PATH = pathlib.Path("verification/reqs.yml")
SIM_REPORT_PATH = pathlib.Path("reports/sim_report.json")
COV_INFO_PATH = pathlib.Path("reports/coverage.info")
TRACE_CSV_PATH = pathlib.Path("reports/trace.csv")
TRACE_JSON_PATH = pathlib.Path("reports/trace.json")

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc


def load_requirements() -> List[Dict]:
    data = yaml.safe_load(REQ_PATH.read_text(encoding="utf-8"))
    return data.get("requirements", [])


def load_sim_report() -> Dict:
    if not SIM_REPORT_PATH.exists():
        return {"status": "unknown", "failures": []}
    return json.loads(SIM_REPORT_PATH.read_text(encoding="utf-8"))


def build_rows(reqs: List[Dict], sim_report: Dict, cov_summary: Dict, per_req_map: Dict[str, Dict]) -> List[Dict]:
    status = sim_report.get("status", "unknown")
    failures = sim_report.get("failures", [])
    failing_rids = {entry.get("req") for entry in failures}
    rows: List[Dict] = []
    cov_line = cov_summary.get("line")
    cov_toggle = cov_summary.get("toggle")
    for req in reqs:
        rid = req.get("id")
        per_req = per_req_map.get(rid, {})
        line_cov = per_req.get("line", cov_line)
        toggle_cov = per_req.get("toggle", cov_toggle)
        parts = []
        if line_cov is not None:
            parts.append(f"line {line_cov:.2%}")
        if toggle_cov is not None:
            parts.append(f"toggle {toggle_cov:.2%}")
        cov_str = ", ".join(parts) if parts else "n/a"
        rows.append(
            {
                "req": rid,
                "text": req.get("text", ""),
                "tested": True,
                "passed": status == "pass" and rid not in failing_rids,
                "coverage": cov_str,
            }
        )
    return rows


def write_csv(rows: List[Dict]) -> None:
    TRACE_CSV_PATH.parent.mkdir(parents=True, exist_ok=True)
    with TRACE_CSV_PATH.open("w", encoding="utf-8", newline="") as fh:
        writer = csv.DictWriter(fh, fieldnames=["req", "tested", "passed", "coverage"])
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row[k] for k in writer.fieldnames})


def write_json(rows: List[Dict]) -> None:
    payload = {"schema": 1, "rows": rows}
    TRACE_JSON_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def main() -> None:
    if not REQ_PATH.exists():
        raise SystemExit(f"Missing requirements file {REQ_PATH}")
    reqs = load_requirements()
    sim_report = load_sim_report()
    cov_summary = {}
    cov_json_path = pathlib.Path("reports/coverage.json")
    if cov_json_path.exists():
        cov_summary = json.loads(cov_json_path.read_text())
    cov_per_req_map: Dict[str, Dict] = {}
    cov_per_req_path = pathlib.Path("reports/coverage_per_req.json")
    if cov_per_req_path.exists():
        cov_per_data = json.loads(cov_per_req_path.read_text())
        for entry in cov_per_data.get("requirements", []):
            cov_per_req_map[entry.get("id")] = entry
    rows = build_rows(reqs, sim_report, cov_summary, cov_per_req_map)
    write_csv(rows)
    write_json(rows)
    print(f"Wrote {TRACE_CSV_PATH} and {TRACE_JSON_PATH}")


if __name__ == "__main__":
    main()
