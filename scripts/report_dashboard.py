#!/usr/bin/env python3
"""Generate Markdown and HTML verification dashboards."""
from __future__ import annotations

import argparse
import datetime as _dt
import html
import json
import pathlib
from typing import Any, Dict, List, Tuple

try:
    import yaml
except ModuleNotFoundError as exc:
    raise SystemExit("PyYAML is required: pip install pyyaml") from exc


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build verification dashboards")
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports"))
    parser.add_argument("--reqs", type=pathlib.Path, default=pathlib.Path("verification/reqs.yml"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports"))
    return parser.parse_args()


def _load_json(path: pathlib.Path) -> dict:
    if not path.exists():
        return {}
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return {}


def _load_reqs(path: pathlib.Path) -> List[Dict[str, Any]]:
    if not path.exists():
        return []
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8")) or {}
    except yaml.YAMLError as exc:
        raise SystemExit(f"Failed to parse requirements file {path}: {exc}") from exc
    reqs = data.get("requirements", [])
    return reqs if isinstance(reqs, list) else []


def _format_percent(value: Any) -> str:
    try:
        return f"{float(value) * 100:.2f}%"
    except (TypeError, ValueError):
        return "n/a"


def _build_requirement_rows(
    reqs: List[Dict[str, Any]],
    coverage: Dict[str, Any],
    sim_failures: set[str],
) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    coverage_map = {
        entry.get("id"): entry
        for entry in coverage.get("requirements", [])
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }
    for req in reqs:
        rid = req.get("id")
        if not isinstance(rid, str):
            continue
        text = req.get("text", "")
        cov_entry = coverage_map.get(rid, {})
        coverage_str = "line {line}, toggle {toggle}".format(
            line=_format_percent(cov_entry.get("line")),
            toggle=_format_percent(cov_entry.get("toggle")),
        )
        tags = ", ".join(req.get("tags", [])) if isinstance(req.get("tags"), list) else ""
        status = "✅" if rid not in sim_failures else "❌"
        rows.append(
            {
                "req": rid,
                "status": status,
                "coverage": coverage_str,
                "text": text,
                "tags": tags,
            }
        )
    return rows


def _write_markdown(
    out_dir: pathlib.Path,
    coverage: dict,
    rows: List[Dict[str, str]],
    sim: dict,
    slices: List[Tuple[str, str]],
) -> str:
    timestamp = _dt.datetime.utcnow().replace(microsecond=0).isoformat() + "Z"
    line_cov = _format_percent(coverage.get("line"))
    toggle_cov = _format_percent(coverage.get("toggle"))
    status = sim.get("status", "unknown").upper()
    failures = len(sim.get("failures", []))

    lines = [
        "# Verification Dashboard",
        "",
        f"_Generated {timestamp}_",
        "",
        "## Simulation",
        f"- Status: **{status}**",
        f"- Failures: {failures}",
        "",
        "## Coverage",
        f"- Line: {line_cov}",
        f"- Toggle: {toggle_cov}",
        "",
        "## Requirements",
        "| Req | Status | Tags | Coverage | Description |",
        "| --- | --- | --- | --- | --- |",
    ]
    if rows:
        for row in rows:
            lines.append(
                f"| {row['req']} | {row['status']} | {row['tags'] or 'n/a'} | {row['coverage']} | {row['text']} |"
            )
    else:
        lines.append("| _n/a_ | _n/a_ | _n/a_ | n/a | No requirements parsed |")
    lines.append("")
    if slices:
        lines.append("## Waveform Slices")
        for name, rel in slices:
            lines.append(f"- [{name}]({rel})")
        lines.append("")
    content = "\n".join(lines) + "\n"
    (out_dir / "dashboard.md").write_text(content, encoding="utf-8")
    return content


def _write_html(
    out_dir: pathlib.Path,
    coverage: dict,
    rows: List[Dict[str, str]],
    sim: dict,
    slices: List[Tuple[str, str]],
) -> str:
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
            f"<td>{html.escape(row['tags'] or 'n/a')}</td>"
            f"<td>{html.escape(row['coverage'])}</td>"
            f"<td>{html.escape(row['text'])}</td>"
            "</tr>"
        )
    if not rows_html:
        rows_html.append("<tr><td colspan=5>No requirements parsed</td></tr>")

    if slices:
        slice_items = ''.join(
            f'<li><a href="{html.escape(path)}">{html.escape(name)}</a></li>'
            for name, path in slices
        )
        slices_html = f'<section class="section"><h2>Waveform Slices</h2><ul>{slice_items}</ul></section>'
    else:
        slices_html = ''

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
.badge {{ display: inline-block; margin-right: 0.5rem; padding: 0.2rem 0.4rem; border-radius: 4px; background: #eef; }}
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
        <tr><th>Req</th><th>Status</th><th>Tags</th><th>Coverage</th><th>Description</th></tr>
      </thead>
      <tbody>
        {''.join(rows_html)}
      </tbody>
    </table>
  </section>
  {slices_html}
</body>
</html>
"""
    html_text = body.strip() + "\n"
    (out_dir / "dashboard.html").write_text(html_text, encoding="utf-8")
    return html_text


def main() -> None:
    args = parse_args()
    reports_dir = args.reports
    out_dir = args.out
    out_dir.mkdir(parents=True, exist_ok=True)

    coverage = _load_json(reports_dir / "coverage.json")
    per_req_cov = _load_json(reports_dir / "coverage_per_req.json")
    sim = _load_json(reports_dir / "sim_report.json")
    reqs = _load_reqs(args.reqs)

    failure_ids = {
        str(entry.get("req"))
        for entry in sim.get("failures", [])
        if isinstance(entry, dict) and isinstance(entry.get("req"), str)
    }
    rows = _build_requirement_rows(reqs, per_req_cov, failure_ids)

    slices: List[Tuple[str, str]] = []
    slices_dir = reports_dir / "slices"
    if slices_dir.exists():
        for png in sorted(slices_dir.glob("*.png")):
            rel = png.relative_to(reports_dir)
            slices.append((png.stem, rel.as_posix()))

    markdown = _write_markdown(out_dir, coverage, rows, sim, slices)
    html_text = _write_html(out_dir, coverage, rows, sim, slices)

    site_dir = reports_dir / "site"
    site_dir.mkdir(parents=True, exist_ok=True)
    (site_dir / "index.html").write_text(html_text, encoding="utf-8")
    (site_dir / "dashboard.html").write_text(html_text, encoding="utf-8")
    (site_dir / "dashboard.md").write_text(markdown, encoding="utf-8")


if __name__ == "__main__":
    main()
