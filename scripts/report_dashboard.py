#!/usr/bin/env python3
"""Generate Markdown and HTML verification dashboards."""
from __future__ import annotations

import argparse
import datetime as _dt
import html
import json
import os
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


def _fraction(value: Any) -> float | None:
    if value is None:
        return None
    if isinstance(value, str):
        try:
            value = float(value)
        except ValueError:
            return None
    if isinstance(value, (int, float)):
        if value > 1:
            return float(value) / 100.0
        return float(value)
    return None


def _gate_entry(name: str, status: bool | None, detail: str) -> Dict[str, str]:
    if status is True:
        icon = "PASS"
    elif status is False:
        icon = "FAIL"
    else:
        icon = "INFO"
    return {"name": name, "icon": icon, "detail": detail, "status": status}


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
    gates: List[Dict[str, str]],
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
        "## Gates",
    ]
    if gates:
        for gate in gates:
            lines.append(f"- {gate['icon']} {gate['name']}: {gate['detail']}")
    else:
        lines.append("- n/a")
    lines.extend(
        [
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
    )
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
    gates: List[Dict[str, str]],
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

    if gates:
        gates_html = ''.join(
            f"<li>{html.escape(gate['icon'])} {html.escape(gate['name'])}: {html.escape(gate['detail'])}</li>"
            for gate in gates
        )
    else:
        gates_html = '<li>n/a</li>'

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
    <h2>Gates</h2>
    <ul>
      {gates_html}
    </ul>
  </section>
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


POLICIES_PATH = pathlib.Path(os.environ.get("POLICIES", "policies.yml"))


def _collect_gate_summary(
    reports_dir: pathlib.Path,
    coverage: Dict[str, Any],
    per_req_cov: Dict[str, Any],
    sim: Dict[str, Any],
    reqs: List[Dict[str, Any]],
) -> List[Dict[str, str]]:
    summary: List[Dict[str, str]] = []

    if POLICIES_PATH.exists():
        try:
            policies = yaml.safe_load(POLICIES_PATH.read_text(encoding="utf-8")) or {}
        except yaml.YAMLError:
            policies = {}
    else:
        policies = {}

    coverage_policy = policies.get("coverage", {}) if isinstance(policies, dict) else {}
    synth_policy = policies.get("synth", {}) if isinstance(policies, dict) else {}

    sim_status = sim.get("status")
    if isinstance(sim_status, str):
        status_norm = sim_status.lower()
        if status_norm in {"pass", "ok", "passed"}:
            summary.append(_gate_entry("Simulation", True, sim_status.upper()))
        elif status_norm:
            summary.append(_gate_entry("Simulation", False, sim_status.upper()))
        else:
            summary.append(_gate_entry("Simulation", None, "n/a"))
    else:
        summary.append(_gate_entry("Simulation", None, "n/a"))

    line_target = _fraction(coverage_policy.get("line"))
    line_value = coverage.get("line")
    if line_target is not None and isinstance(line_value, (int, float)):
        ok = line_value + 1e-9 >= line_target
        detail = f"{_format_percent(line_value)} (>= {_format_percent(line_target)})"
        summary.append(_gate_entry("Line coverage", ok, detail))
    elif isinstance(line_value, (int, float)):
        summary.append(_gate_entry("Line coverage", None, _format_percent(line_value)))
    else:
        summary.append(_gate_entry("Line coverage", None, "n/a"))

    toggle_target = _fraction(coverage_policy.get("toggle"))
    toggle_value = coverage.get("toggle")
    if toggle_target is not None and isinstance(toggle_value, (int, float)):
        ok = toggle_value + 1e-9 >= toggle_target
        detail = f"{_format_percent(toggle_value)} (>= {_format_percent(toggle_target)})"
        summary.append(_gate_entry("Toggle coverage", ok, detail))
    elif isinstance(toggle_value, (int, float)):
        summary.append(_gate_entry("Toggle coverage", None, _format_percent(toggle_value)))
    else:
        summary.append(_gate_entry("Toggle coverage", None, "n/a"))

    default_target = _fraction(coverage_policy.get("per_requirement"))
    overrides_raw = coverage_policy.get("per_req_overrides", {}) if isinstance(coverage_policy, dict) else {}
    override_map = {
        str(key).lower(): _fraction(val)
        for key, val in overrides_raw.items()
        if _fraction(val) is not None
    }
    per_req_entries = {
        entry.get("id"): entry
        for entry in per_req_cov.get("requirements", [])
        if isinstance(entry, dict) and isinstance(entry.get("id"), str)
    }
    tracked_requirements = [req for req in reqs if isinstance(req, dict) and isinstance(req.get("id"), str)]
    if tracked_requirements and (default_target is not None or override_map):
        failing: List[str] = []
        for req in tracked_requirements:
            rid = req["id"]
            priority = str(req.get("priority", "")).lower()
            target = override_map.get(priority, default_target)
            if target is None:
                continue
            entry = per_req_entries.get(rid, {})
            line_val = entry.get("line")
            fraction = float(line_val) if isinstance(line_val, (int, float)) else 0.0
            if fraction + 1e-9 < target:
                failing.append(rid)
        if failing:
            detail = "Missing coverage: " + ", ".join(failing[:5])
            if len(failing) > 5:
                detail += ", …"
            summary.append(_gate_entry("Per-requirement coverage", False, detail))
        else:
            target_percent = _format_percent(default_target) if default_target is not None else "policy override"
            summary.append(_gate_entry("Per-requirement coverage", True, f"Targets met ({target_percent})"))
    else:
        summary.append(_gate_entry("Per-requirement coverage", None, "n/a"))

    synth_report = _load_json(reports_dir / "synth_report.json")
    has_latch = synth_report.get("has_latch")
    forbid_latches = bool(synth_policy.get("forbid_latches", False)) if isinstance(synth_policy, dict) else False
    if forbid_latches and isinstance(has_latch, bool):
        summary.append(_gate_entry("Synthesis latches", not has_latch, "no latches inferred" if not has_latch else "latches detected"))
    elif isinstance(has_latch, bool):
        detail = "no latches inferred" if not has_latch else "latches detected"
        summary.append(_gate_entry("Synthesis latches", None, detail))
    else:
        summary.append(_gate_entry("Synthesis latches", None, "n/a"))

    formal_summary = _load_json(reports_dir / "formal" / "summary.json")
    tasks = [task for task in formal_summary.get("tasks", []) if isinstance(task, dict)]
    if tasks:
        failing = [task.get("name", "?") for task in tasks if not task.get("optional") and task.get("status") != "PASS"]
        if failing:
            summary.append(_gate_entry("Formal", False, "Failed tasks: " + ", ".join(failing)))
        else:
            summary.append(_gate_entry("Formal", True, "All required profiles pass"))
    else:
        summary.append(_gate_entry("Formal", None, "n/a"))

    return summary


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

    gates = _collect_gate_summary(reports_dir, coverage, per_req_cov, sim, reqs)

    markdown = _write_markdown(out_dir, coverage, rows, sim, slices, gates)
    html_text = _write_html(out_dir, coverage, rows, sim, slices, gates)

    site_dir = reports_dir / "site"
    site_dir.mkdir(parents=True, exist_ok=True)
    (site_dir / "index.html").write_text(html_text, encoding="utf-8")
    (site_dir / "dashboard.html").write_text(html_text, encoding="utf-8")
    (site_dir / "dashboard.md").write_text(markdown, encoding="utf-8")


if __name__ == "__main__":
    main()
