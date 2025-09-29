#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib

info_path = pathlib.Path("reports/coverage.info")
if not info_path.exists():
    raise SystemExit("coverage.info not found; run make cov first")

text = info_path.read_text(encoding="utf-8", errors="ignore")

line_total = line_hit = 0
branch_total = branch_hit = 0

for line in text.splitlines():
    if line.startswith("DA:"):
        try:
            _, count_str = line.split(",", 1)
            line_total += 1
            if int(count_str) > 0:
                line_hit += 1
        except ValueError:
            continue
    elif line.startswith("BRDA:"):
        parts = line.split(",")
        if len(parts) == 4:
            count = parts[3].strip()
            if count != "-":
                branch_total += 1
                if int(count) > 0:
                    branch_hit += 1

coverage = {
    "schema": 1,
    "line": round(line_hit / line_total, 4) if line_total else None,
    "toggle": round(branch_hit / branch_total, 4) if branch_total else None,
    "line_total": line_total,
    "line_hit": line_hit,
    "branch_total": branch_total,
    "branch_hit": branch_hit,
}

out_path = pathlib.Path("reports/coverage.json")
out_path.write_text(json.dumps(coverage, indent=2), encoding="utf-8")
print(f"Wrote {out_path}", coverage)
