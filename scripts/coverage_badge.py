#!/usr/bin/env python3
"""Create a simple SVG badge for line coverage."""
from __future__ import annotations

import json
import pathlib

COVERAGE_JSON = pathlib.Path("reports/coverage.json")
BADGE_PATH = pathlib.Path("reports/coverage_badge.svg")


COLORS = [
    (90.0, "#4c1"),
    (75.0, "#dfb317"),
    (0.0, "#e05d44"),
]


def _load_line_percent() -> float | None:
    if not COVERAGE_JSON.exists():
        return None
    try:
        data = json.loads(COVERAGE_JSON.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None
    value = data.get("line")
    if value is None:
        return None
    try:
        return float(value) * 100.0
    except (TypeError, ValueError):
        return None


def _pick_color(percent: float | None) -> str:
    if percent is None:
        return "#9f9f9f"
    for threshold, color in COLORS:
        if percent >= threshold:
            return color
    return COLORS[-1][1]


def main() -> None:
    percent = _load_line_percent()
    value_text = "n/a" if percent is None else f"{percent:.1f}%"
    color = _pick_color(percent)
    svg = f"""
<svg xmlns="http://www.w3.org/2000/svg" width="150" height="20" role="img" aria-label="coverage: {value_text}">
  <title>coverage: {value_text}</title>
  <linearGradient id="smooth" x2="0" y2="100%">
    <stop offset="0" stop-color="#bbb" stop-opacity=".1"/>
    <stop offset="1" stop-opacity=".1"/>
  </linearGradient>
  <mask id="round">
    <rect width="150" height="20" rx="3" fill="#fff"/>
  </mask>
  <g mask="url(#round)">
    <rect width="80" height="20" fill="#555"/>
    <rect x="80" width="70" height="20" fill="{color}"/>
    <rect width="150" height="20" fill="url(#smooth)"/>
  </g>
  <g fill="#fff" text-anchor="middle" font-family="DejaVu Sans, Verdana, Geneva, sans-serif" font-size="11">
    <text x="40" y="15" fill="#010101" fill-opacity=".3">coverage</text>
    <text x="40" y="14">coverage</text>
    <text x="115" y="15" fill="#010101" fill-opacity=".3">{value_text}</text>
    <text x="115" y="14">{value_text}</text>
  </g>
</svg>
"""
    BADGE_PATH.write_text(svg.strip() + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
