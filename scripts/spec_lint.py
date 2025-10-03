#!/usr/bin/env python3
"""Lint docs/spec.md for template compliance."""
from __future__ import annotations

import argparse
import pathlib
import re
from typing import Iterable

from spec2tests import Requirement, extract_requirements  # type: ignore

TAG_RE = re.compile(r"^[a-z0-9_-]+$")


def lint_requirements(requirements: Iterable[Requirement]) -> None:
    seen_priorities = set()
    for req in requirements:
        seen_priorities.add(req.priority)
        for tag in req.tags:
            if not TAG_RE.fullmatch(tag):
                raise SystemExit(
                    f"Requirement {req.rid} tag '{tag}' must match {TAG_RE.pattern}"
                )
    if "must" not in seen_priorities:
        raise SystemExit("At least one requirement must be tagged with priority 'must'")


def main() -> None:
    parser = argparse.ArgumentParser(description="Lint requirements format")
    parser.add_argument("--spec", type=pathlib.Path, default=pathlib.Path("docs/spec.md"))
    args = parser.parse_args()

    if not args.spec.exists():
        raise SystemExit(f"Spec file {args.spec} not found")

    text = args.spec.read_text(encoding="utf-8")
    requirements = extract_requirements(text)
    lint_requirements(requirements)
    print(f"lint ok: {len(requirements)} requirements")


if __name__ == "__main__":
    main()
