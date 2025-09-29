#!/usr/bin/env python3
from __future__ import annotations

import copy
import json
import pathlib
import re

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

REQ_PATH = pathlib.Path("verification/reqs.yml")
SIM_REPORT_PATH = pathlib.Path("reports/sim_report.json")
COVERAGE_JSON_PATH = pathlib.Path("reports/coverage.json")
SIM_LOG_PATH = pathlib.Path("reports/sim.log")
TB_PATH = pathlib.Path("tb/top_tb.sv")
OUT_PATH = pathlib.Path("reports/coverage_per_req.json")

BIN_LABELS = ("zero", "mid", "max")
CROSS_LABELS = tuple(f"{a}_{b}" for a in BIN_LABELS for b in BIN_LABELS)
COVBIN_RE = re.compile(r"\[COVBIN\]\s+(?P<req>\S+)\s+a=(?P<a>\d+)\s+b=(?P<b>\d+)")


def infer_width_from_tb(tb_path: pathlib.Path) -> int:
    if not tb_path.exists():
        return 8
    match = re.search(r"localparam\\s+int\\s+W\\s*=\\s*(\\d+);", tb_path.read_text(encoding="utf-8"))
    if match:
        return int(match.group(1))
    return 8


def classify_bin(value: int, max_value: int) -> str:
    if value == 0:
        return "zero"
    if value == max_value:
        return "max"
    return "mid"


def init_bin_counts() -> dict[str, dict[str, int]]:
    return {
        "a": {label: 0 for label in BIN_LABELS},
        "b": {label: 0 for label in BIN_LABELS},
        "cross": {label: 0 for label in CROSS_LABELS},
    }


def parse_covbin_log(log_path: pathlib.Path, max_value: int) -> dict[str, dict[str, dict[str, int]]]:
    if not log_path.exists():
        return {}
    data: dict[str, dict[str, dict[str, int]]] = {}
    for match in COVBIN_RE.finditer(log_path.read_text(encoding="utf-8")):
        rid = match.group("req")
        aval = int(match.group("a"))
        bval = int(match.group("b"))
        bins = data.setdefault(rid, init_bin_counts())
        a_bin = classify_bin(aval, max_value)
        b_bin = classify_bin(bval, max_value)
        bins["a"][a_bin] += 1
        bins["b"][b_bin] += 1
        cross_key = f"{a_bin}_{b_bin}"
        bins["cross"][cross_key] += 1
    return data


def bin_coverage(counts: dict[str, dict[str, int]]) -> dict[str, float]:
    coverage = {"a": 0.0, "b": 0.0, "cross": 0.0}
    if not counts:
        return coverage
    a_hits = sum(1 for label in BIN_LABELS if counts["a"].get(label, 0) > 0)
    b_hits = sum(1 for label in BIN_LABELS if counts["b"].get(label, 0) > 0)
    cross_hits = sum(1 for label in CROSS_LABELS if counts["cross"].get(label, 0) > 0)
    coverage["a"] = a_hits / len(BIN_LABELS)
    coverage["b"] = b_hits / len(BIN_LABELS)
    coverage["cross"] = cross_hits / len(CROSS_LABELS)
    return coverage

if not REQ_PATH.exists() or not SIM_REPORT_PATH.exists():
    raise SystemExit("Missing requirements or simulation report; run make report first")

reqs = yaml.safe_load(REQ_PATH.read_text(encoding="utf-8"))
reqs_list = reqs.get("requirements", [])
sim_report = json.loads(SIM_REPORT_PATH.read_text(encoding="utf-8"))
coverage_summary = {}
if COVERAGE_JSON_PATH.exists():
    coverage_summary = json.loads(COVERAGE_JSON_PATH.read_text(encoding="utf-8"))

samples = sim_report.get("coverage_samples", {})
total_samples = sum(samples.values())
line_global = coverage_summary.get("line")
toggle_global = coverage_summary.get("toggle")

width = infer_width_from_tb(TB_PATH)
max_value = (1 << width) - 1
covbin_counts_map = parse_covbin_log(SIM_LOG_PATH, max_value)

requirements = []
for req in reqs_list:
    rid = req.get("id")
    sample_count = samples.get(rid, 0)
    line_cov = line_global if sample_count > 0 and line_global is not None else 0.0
    toggle_cov = toggle_global if sample_count > 0 and toggle_global is not None else 0.0
    bin_counts = copy.deepcopy(covbin_counts_map.get(rid, init_bin_counts()))
    bin_cov = bin_coverage(bin_counts)
    requirements.append(
        {
            "id": rid,
            "samples": sample_count,
            "line": line_cov,
            "toggle": toggle_cov,
            "bins": {
                "counts": bin_counts,
                "coverage": bin_cov,
            },
        }
    )

payload = {
    "schema": 1,
    "total_samples": total_samples,
    "requirements": requirements,
}

OUT_PATH.write_text(json.dumps(payload, indent=2), encoding="utf-8")
print(f"Wrote {OUT_PATH}")
