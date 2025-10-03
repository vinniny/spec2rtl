#!/usr/bin/env python3
"""Inject generic mutations into RTL sources for mutation testing."""
from __future__ import annotations

import argparse
import json
import pathlib
import re
from dataclasses import dataclass
from typing import Callable, List


@dataclass
class MutationSpec:
    name: str
    description: str
    pattern: re.Pattern[str]
    replacer: Callable[[re.Match[str]], str]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Generate mutated RTL variants")
    parser.add_argument("--rtl", type=pathlib.Path, default=pathlib.Path("rtl"), help="Directory containing source RTL")
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("mutants"), help="Directory to emit mutants")
    parser.add_argument("--limit", type=int, default=20, help="Maximum mutants to generate")
    return parser.parse_args()


def build_specs() -> List[MutationSpec]:
    return [
        MutationSpec(
            name="flip_reset_condition",
            description="Invert an active-low reset condition",
            pattern=re.compile(r"if\s*\(\s*!\s*(?P<sig>[a-zA-Z_][\w]*)\s*\)"),
            replacer=lambda m: f"if ({m.group('sig')})",
        ),
        MutationSpec(
            name="blocking_assignment",
            description="Convert a non-blocking assignment to blocking",
            pattern=re.compile(r"(?P<lhs>^\s*[a-zA-Z_][\w\[\]\.']*)\s*<=\s*", re.MULTILINE),
            replacer=lambda m: f"{m.group('lhs')} = ",
        ),
        MutationSpec(
            name="subtractive_math",
            description="Replace an addition with subtraction",
            pattern=re.compile(r"(?P<lhs>[\w)\]]+)\s*\+\s*(?P<rhs>[\w)\]]+)"),
            replacer=lambda m: f"{m.group('lhs')} - {m.group('rhs')}",
        ),
    ]


def generate_mutants(args: argparse.Namespace) -> list[dict[str, str]]:
    specs = build_specs()
    rtl_files = sorted(args.rtl.glob("*.sv"))
    args.out.mkdir(parents=True, exist_ok=True)
    mutants: list[dict[str, str]] = []
    counter = 1

    for rtl in rtl_files:
        source = rtl.read_text(encoding="utf-8")
        for spec in specs:
            mutated, count = spec.pattern.subn(spec.replacer, source, count=1)
            if count == 0:
                continue
            mutant_id = f"MUT-{counter:03d}"
            out_path = args.out / f"{rtl.stem}__{spec.name}.sv"
            out_path.write_text(mutated, encoding="utf-8")
            mutants.append(
                {
                    "id": mutant_id,
                    "source": str(rtl),
                    "mutation": spec.name,
                    "description": spec.description,
                    "path": str(out_path),
                }
            )
            counter += 1
            if counter > args.limit:
                return mutants
    return mutants


def write_manifest(mutants: list[dict[str, str]], out_dir: pathlib.Path) -> None:
    manifest = {
        "schema": 1,
        "count": len(mutants),
        "mutations": mutants,
    }
    (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=2), encoding="utf-8")


def main() -> None:
    args = parse_args()
    mutants = generate_mutants(args)
    write_manifest(mutants, args.out)
    for entry in mutants:
        print(entry["path"])


if __name__ == "__main__":
    main()
