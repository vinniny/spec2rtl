#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib
import re
from typing import Any, Dict

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc

from json_schemas import SchemaError, validate_synth


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Summarise Yosys synthesis log")
    parser.add_argument("--log", type=pathlib.Path, default=pathlib.Path("synth/yosys.log"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/synth_report.json"))
    parser.add_argument("--policies", type=pathlib.Path, default=pathlib.Path("policies.yml"))
    return parser.parse_args()


def load_policies(path: pathlib.Path) -> Dict[str, Any]:
    if not path.exists():
        return {}
    try:
        return yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise SystemExit(f"Failed to parse policies at {path}: {exc}") from exc


def summarise_log(log_path: pathlib.Path) -> Dict[str, Any]:
    if not log_path.exists():
        raise SystemExit(f"Yosys log not found: {log_path}")

    text = log_path.read_text(encoding="utf-8", errors="ignore")
    cells: Dict[str, int] = {}
    cell_re = re.compile(r"^\s+([\w$\.]+)\s+(\d+)\s*$")
    for line in text.splitlines():
        match = cell_re.match(line)
        if match:
            cells[match.group(1)] = int(match.group(2))

    warnings = [line for line in text.splitlines() if re.search(r"warning", line, re.IGNORECASE)]
    has_latch = any("latch" in w.lower() for w in warnings) or any("$_DLATCH" in name for name in cells)

    return {
        "schema": 1,
        "cells": cells,
        "warnings": warnings,
        "has_latch": has_latch,
    }


def main() -> None:
    args = parse_args()
    summary = summarise_log(args.log)
    try:
        validate_synth(summary)
    except SchemaError as exc:
        raise SystemExit(f"synth_report.json schema validation failed: {exc}") from exc

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote {args.out}")

    policies = load_policies(args.policies)
    synth_policy = policies.get("synth", {}) if isinstance(policies, dict) else {}
    forbid_latches = bool(synth_policy.get("forbid_latches"))

    if forbid_latches and summary.get("has_latch"):
        raise SystemExit("Synthesis detected latch structures; forbidden by policy")


if __name__ == "__main__":
    main()
