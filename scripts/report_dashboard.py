#!/usr/bin/env python3
"""Generate Markdown and HTML verification dashboards."""
from __future__ import annotations

import datetime as _dt
import html
import json
import pathlib
from typing import Any, Dict, List

COVERAGE_JSON = pathlib.Path("reports/coverage.json")
TRACE_JSON = pathlib.Path("reports/trace.json")
SIM_REPORT = pathlib.Path("reports/sim_report.json")
DASHBOARD_MD = pathlib.Path("reports/dashboard.md")
DASHBOARD_HTML = pathlib.Path("reports/dashboard.html")
SITE_DIR = pathlib.Path("reports/site")


def _load_json(path: pathlib.Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _format_percent(value: Any) -> str:
    try:
        return f"{float(value) * 100:.2f}%"
    except (TypeError, ValueError):
        return "n/a"


def _build_requirement_rows(trace_data: dict) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    for row in trace_data.get("rows", []):
        req = str(row.get("req", "?"))
        passed = bool(row.get("passed"))
        status = "✅" if passed else "❌"
        coverage = row.get("coverage") or "n/a"
        text = row.get("text", "")
        rows.append({
            "req": req,
            "status": status,
            "coverage": coverage,
            "text": text,
        })
    return rows


def _write_markdown(coverage: dict, rows: List[Dict[str, str]], sim: dict) -> str:
    timestamp = _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"
    line_cov = _format_percent(coverage.get("line"))
    toggle_cov = _format_percent(coverage.get("toggle"))
    status = sim.get("status", "unknown").upper()

    lines = [
        "# Verification Dashboard",
        "",
        f"_Generated {timestamp}_",
        "",
        "## Simulation",
        f"- Status: **{status}**",
        f"- Failures: {len(sim.get('failures', []))}",
        "",
        "## Coverage",
        f"- Line: {line_cov}",
        f"- Toggle: {toggle_cov}",
        "",
        "## Requirements",
        "| Req | Status | Coverage | Description |",
        "| --- | --- | --- | --- |",
    ]
    if rows:
        for row in rows:
            lines.append(
                f"| {row['req']} | {row['status']} | {row['coverage']} | {row['text']} |"
            )
    else:
        lines.append("| _n/a_ | _n/a_ | _n/a_ | No trace data |")
    lines.append("")
    content = "\n".join(lines) + "\n"
    DASHBOARD_MD.write_text(content, encoding="utf-8")
    return content


def _write_html(coverage: dict, rows: List[Dict[str, str]], sim: dict) -> str:
    timestamp = _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"
    line_cov = _format_percent(coverage.get("line"))
    toggle_cov = _format_percent(coverage.get("toggle"))
    status = html.escape(str(sim.get("status", "unknown")).upper())
    failure_count = len(sim.get("failures", []))

    rows_html = []
    for row in rows:
        rows_html.append(
            "<tr>"
            f"<td>{html.escape(row['req'])}</td>"
            f"<td>{html.escape(row['status'])}</td>"
            f"<td>{html.escape(row['coverage'])}</td>"
            f"<td>{html.escape(row['text'])}</td>"
            "</tr>"
        )
    if not rows_html:
        rows_html.append(
            "<tr><td colspan=4>No trace data</td></tr>"
        )

    body = f"""
<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8" />
<title>Verification Dashboard</title>
<style>
body {{ font-family: Arial, sans-serif; margin: 1.5rem; }}
h1 {{ margin-bottom: 0.2rem; }}
table {{ border-collapse: collapse; width: 100%; margin-top: 1rem; }}
th, td {{ border: 1px solid #ccc; padding: 0.4rem; text-align: left; }}
th {{ background: #f0f0f0; }}
.section {{ margin-top: 1.5rem; }}
</style>
</head>
<body>
  <h1>Verification Dashboard</h1>
  <p><em>Generated {timestamp}</em></p>
  <section class="section">
    <h2>Simulation</h2>
    <ul>
      <li>Status: <strong>{status}</strong></li>
      <li>Failures: {failure_count}</li>
    </ul>
  </section>
  <section class="section">
    <h2>Coverage</h2>
    <ul>
      <li>Line: {line_cov}</li>
      <li>Toggle: {toggle_cov}</li>
    </ul>
  </section>
  <section class="section">
    <h2>Requirements</h2>
    <table>
      <thead>
        <tr><th>Req</th><th>Status</th><th>Coverage</th><th>Description</th></tr>
      </thead>
      <tbody>
        {''.join(rows_html)}
      </tbody>
    </table>
  </section>
</body>
</html>
"""
    html_text = body.strip() + "\n"
    DASHBOARD_HTML.write_text(html_text, encoding="utf-8")
    return html_text


def main() -> None:
    coverage = _load_json(COVERAGE_JSON)
    trace = _load_json(TRACE_JSON)
    sim = _load_json(SIM_REPORT)
    rows = _build_requirement_rows(trace)
    markdown = _write_markdown(coverage, rows, sim)
    html_text = _write_html(coverage, rows, sim)

    SITE_DIR.mkdir(parents=True, exist_ok=True)
    (SITE_DIR / "index.html").write_text(html_text, encoding="utf-8")
    (SITE_DIR / "dashboard.html").write_text(html_text, encoding="utf-8")
    (SITE_DIR / "dashboard.md").write_text(markdown, encoding="utf-8")


if __name__ == "__main__":
    main()
