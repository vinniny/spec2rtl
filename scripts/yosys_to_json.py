#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib
import re

LOG_PATH = pathlib.Path("synth/yosys.log")
REPORTS_DIR = pathlib.Path("reports")
OUT_PATH = REPORTS_DIR / "synth_report.json"

REPORTS_DIR.mkdir(parents=True, exist_ok=True)

if not LOG_PATH.exists():
    OUT_PATH.write_text(json.dumps({"schema": 1, "error": "log missing"}, indent=2), encoding="utf-8")
    raise SystemExit("Yosys log not found")

text = LOG_PATH.read_text(encoding="utf-8", errors="ignore")

cells = {}
cell_re = re.compile(r"^\s+([\w$\.]+)\s+(\d+)\s*$")
for line in text.splitlines():
    m = cell_re.match(line)
    if m:
        cells[m.group(1)] = int(m.group(2))

warnings = [line for line in text.splitlines() if re.search(r"warning", line, re.IGNORECASE)]
summary = {
    "schema": 1,
    "cells": cells,
    "warnings": warnings,
    "has_latch": any("latch" in w.lower() for w in warnings) or any("$_DLATCH" in name for name in cells),
}

OUT_PATH.write_text(json.dumps(summary, indent=2), encoding="utf-8")
print(f"Wrote {OUT_PATH}")
