#!/usr/bin/env python3
from __future__ import annotations

import argparse
import copy
import json
import pathlib
import re
from typing import Dict

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

from json_schemas import SchemaError, validate_coverage_per_req

BIN_LABELS = ("zero", "mid", "max")
CROSS_LABELS = tuple(f"{a}_{b}" for a in BIN_LABELS for b in BIN_LABELS)
COVBIN_RE = re.compile(r"\[COVBIN\]\s+(?P<req>\S+)\s+a=(?P<a>\d+)\s+b=(?P<b>\d+)")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Summarise coverage per requirement")
    parser.add_argument("--reqs", type=pathlib.Path, default=pathlib.Path("verification/reqs.yml"))
    parser.add_argument("--sim", type=pathlib.Path, default=pathlib.Path("reports/sim_report.json"))
    parser.add_argument("--cov", type=pathlib.Path, default=pathlib.Path("reports/coverage.json"))
    parser.add_argument("--log", type=pathlib.Path, default=pathlib.Path("reports/sim.log"))
    parser.add_argument("--tb", type=pathlib.Path, default=pathlib.Path("tb/top_tb.sv"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/coverage_per_req.json"))
    return parser.parse_args()


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


def load_json(path: pathlib.Path) -> Dict[str, object]:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def main() -> None:
    args = parse_args()
    if not args.reqs.exists() or not args.sim.exists():
        raise SystemExit("Missing requirements or simulation report; run make report first")

    reqs = yaml.safe_load(args.reqs.read_text(encoding="utf-8"))
    reqs_list = reqs.get("requirements", [])
    sim_report = load_json(args.sim)
    coverage_summary = load_json(args.cov)

    samples = sim_report.get("coverage_samples", {})
    total_samples = sum(samples.values()) if isinstance(samples, dict) else 0
    line_global = coverage_summary.get("line") if isinstance(coverage_summary, dict) else None
    toggle_global = coverage_summary.get("toggle") if isinstance(coverage_summary, dict) else None

    width = infer_width_from_tb(args.tb)
    max_value = (1 << width) - 1
    covbin_counts_map = parse_covbin_log(args.log, max_value)

    requirements = []
    for req in reqs_list:
        rid = req.get("id")
        if not isinstance(rid, str):
            continue
        sample_count = samples.get(rid, 0) if isinstance(samples, dict) else 0
        line_cov = line_global if sample_count > 0 and isinstance(line_global, (int, float)) else 0.0
        toggle_cov = toggle_global if sample_count > 0 and isinstance(toggle_global, (int, float)) else 0.0
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

    try:
        validate_coverage_per_req(payload)
    except SchemaError as exc:
        raise SystemExit(f"coverage_per_req.json schema validation failed: {exc}") from exc

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
