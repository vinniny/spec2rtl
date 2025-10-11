#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import pathlib

from json_schemas import SchemaError, validate_coverage


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Convert lcov coverage.info to JSON summary")
    parser.add_argument("--in", dest="input", type=pathlib.Path, default=pathlib.Path("reports/coverage.info"))
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/coverage.json"))
    return parser.parse_args()


def compute_coverage(info_path: pathlib.Path) -> dict[str, float | int | None]:
    if not info_path.exists():
        raise SystemExit(f"coverage info not found: {info_path}")

    line_total = line_hit = branch_total = branch_hit = 0
    text = info_path.read_text(encoding="utf-8", errors="ignore")
    fallback_branch_total = fallback_branch_hit = 0

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
        elif line.startswith("BRF:"):
            try:
                fallback_branch_total += int(line.split(":", 1)[1])
            except (IndexError, ValueError):
                continue
        elif line.startswith("BRH:"):
            try:
                fallback_branch_hit += int(line.split(":", 1)[1])
            except (IndexError, ValueError):
                continue

    if branch_total == 0 and fallback_branch_total > 0:
        branch_total = fallback_branch_total
        branch_hit = min(fallback_branch_hit, branch_total)

    return {
        "schema": 1,
        "line": round(line_hit / line_total, 3) if line_total else None,
        "toggle": round(branch_hit / branch_total, 3) if branch_total else None,
        "line_total": line_total,
        "line_hit": line_hit,
        "branch_total": branch_total,
        "branch_hit": branch_hit,
    }


def main() -> None:
    args = parse_args()
    summary = compute_coverage(args.input)
    try:
        validate_coverage(summary)
    except SchemaError as exc:
        raise SystemExit(f"coverage.json schema validation failed: {exc}") from exc

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(summary, indent=2), encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
