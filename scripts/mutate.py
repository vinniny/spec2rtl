#!/usr/bin/env python3
"""Inject simple mutations into the synthesized design for mutation testing."""
from __future__ import annotations

import pathlib
import random
import re
import sys
from typing import Iterable, Tuple

# Mutation candidates: (pattern, replacement) regular expressions.
MUTATIONS: Iterable[Tuple[str, str]] = (
    (r"sum_d\s*=\s*a\s*\+\s*b;", "sum_d = a - b;"),
    (r"sum_d\s*=\s*a\s*\+\s*b;", "sum_d = a ^ b;"),
    (r"sum_d\s*=\s*a\s*\+\s*b;", "sum_d = a & b;"),
    (r"if\s*\(!rst_n\)", "if (rst_n)"),
    (r"sum_q\s*<=\s*sum_d;", "sum_q <= sum_q;"),
    (r"assign\s+y\s*=\s*sum_q;", "assign y = sum_d;"),
    (r"assign\s+y\s*=\s*sum_q;", "assign y = sum_q[6:0];"),
)

SOURCE_PATH = pathlib.Path("rtl/top.sv")
MUTATED_PATH = pathlib.Path("rtl/top_mut.sv")


def select_mutation(mutations: Iterable[Tuple[str, str]]) -> Tuple[str, str]:
    mutations_tuple = tuple(mutations)
    if not mutations_tuple:
        raise ValueError("No mutation patterns configured")
    return random.choice(mutations_tuple)


def main() -> int:
    src = SOURCE_PATH.read_text()
    pattern, replacement = select_mutation(MUTATIONS)

    mutated, count = re.subn(pattern, replacement, src, count=1)
    if count == 0:
        print(f"No mutations applied for pattern: {pattern}", file=sys.stderr)
        return 2

    MUTATED_PATH.write_text(mutated)
    print(MUTATED_PATH.as_posix())
    return 0


if __name__ == "__main__":
    sys.exit(main())
