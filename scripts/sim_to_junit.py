#!/usr/bin/env python3
"""Convert simulation report JSON into a minimal JUnit XML file."""
from __future__ import annotations

import json
import pathlib
from xml.sax.saxutils import escape

SIM_REPORT = pathlib.Path("reports/sim_report.json")
OUTPUT = pathlib.Path("reports/junit.xml")


def main() -> None:
    if not SIM_REPORT.exists():
        raise SystemExit("reports/sim_report.json not found; run make report first")

    report = json.loads(SIM_REPORT.read_text(encoding="utf-8"))
    pass_count = int(report.get("pass_count", 0))
    fail_count = int(report.get("fail_count", 0))
    failures = report.get("failures", []) or []

    total_cases = max(1, pass_count + fail_count)

    lines: list[str] = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<testsuite name="rtl" tests="{total_cases}" failures="{len(failures)}">',
    ]

    if failures:
        for failure in failures:
            name = escape(str(failure.get("req", "unknown")))
            message = escape(str(failure.get("line", "")))
            lines.append(f'  <testcase name="{name}">')
            lines.append(f'    <failure message="{message}"/>')
            lines.append("  </testcase>")
    else:
        status_name = "all" if fail_count == 0 else "summary"
        lines.append(f'  <testcase name="{status_name}"/>')

    lines.append("</testsuite>")

    OUTPUT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{OUTPUT.as_posix()} written")


if __name__ == "__main__":
    main()
