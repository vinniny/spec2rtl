#!/usr/bin/env python3
"""Create a focused waveform slice around the reported failure time."""
from __future__ import annotations

import pathlib
import re
import shutil
import sys
from typing import Iterable

LOG_PATH = pathlib.Path("reports/sim.log")
REPORTS_DIR = pathlib.Path("reports")
OUT_FST = REPORTS_DIR / "fail.fst"
OUT_GTKW = REPORTS_DIR / "fail.gtkw"
SEARCH_PATTERNS: Iterable[str] = (
    "build/sim/obj_dir*/dump.fst",
    "obj_dir_*/dump.fst",
    "dump.fst",
)


def read_failure_time() -> int:
    try:
        text = LOG_PATH.read_text()
    except FileNotFoundError:
        return 0
    match = re.search(r"\[META\]\s+TIME=(\d+)", text)
    return int(match.group(1)) if match else 0


def find_latest_dump() -> pathlib.Path | None:
    latest: pathlib.Path | None = None
    latest_mtime = -1.0
    for pattern in SEARCH_PATTERNS:
        for candidate in pathlib.Path(".").glob(pattern):
            if not candidate.is_file():
                continue
            try:
                mtime = candidate.stat().st_mtime
            except FileNotFoundError:
                continue
            if mtime > latest_mtime:
                latest = candidate
                latest_mtime = mtime
    return latest


def main() -> int:
    fail_time = read_failure_time()
    dump = find_latest_dump()
    if dump is None:
        print("Wave slice: no dump.fst found", file=sys.stderr)
        return 0

    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    shutil.copy(dump, OUT_FST)

    start = max(0, fail_time - 200)
    stop = max(start, fail_time + 200)
    gtkw_content = (
        f"$dumpfile {OUT_FST.as_posix()}\n"
        f"[timestart] {start}\n"
        f"[timestop] {stop}\n"
    )
    OUT_GTKW.write_text(gtkw_content)
    print(f"Wave slice: gtkwave {OUT_FST.as_posix()} {OUT_GTKW.as_posix()}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
