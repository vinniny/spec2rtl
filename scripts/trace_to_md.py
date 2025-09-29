#!/usr/bin/env python3
from __future__ import annotations

import json
import pathlib

TRACE_JSON = pathlib.Path("reports/trace.json")
OUT_MD = pathlib.Path("reports/trace.md")

if not TRACE_JSON.exists():
    raise SystemExit("trace.json not found; run make trace first")

data = json.loads(TRACE_JSON.read_text(encoding="utf-8"))
rows = data.get("rows", [])

lines = ["# Requirement Traceability", ""]
for row in rows:
    rid = row.get("req", "")
    status = "✅" if row.get("passed") else "❌"
    cov = row.get("coverage", row.get("cov", "n/a"))
    text = row.get("text", "")
    lines.append(f"- **{rid}** {status} (cov: {cov}) — {text}")

OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")
print(f"Wrote {OUT_MD}")
