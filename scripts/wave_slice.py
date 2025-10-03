#!/usr/bin/env python3
"""Create a focused waveform slice around the reported failure time."""
from __future__ import annotations

import argparse
import pathlib
import re
import shutil
import sys
import time
from typing import Iterable

DEFAULT_PATTERNS: Iterable[str] = (
    "build/sim/obj_dir*/dump.fst",
    "obj_dir_*/dump.fst",
    "dump.fst",
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Create a waveform slice artifact")
    parser.add_argument("--reports", type=pathlib.Path, default=pathlib.Path("reports"))
    parser.add_argument("--log", type=pathlib.Path)
    parser.add_argument("--label", default="failure")
    parser.add_argument("--patterns", nargs="*", default=list(DEFAULT_PATTERNS))
    return parser.parse_args()


def read_failure_time(log_path: pathlib.Path) -> int:
    try:
        text = log_path.read_text()
    except FileNotFoundError:
        return 0
    match = re.search(r"\[META\]\s+TIME=(\d+)", text)
    return int(match.group(1)) if match else 0


def find_latest_dump(patterns: Iterable[str]) -> pathlib.Path | None:
    latest: pathlib.Path | None = None
    latest_mtime = -1.0
    for pattern in patterns:
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

    reports_dir = args.reports
    log_path = args.log or (reports_dir / "sim.log")
    fail_time = read_failure_time(log_path)
    dump = find_latest_dump(args.patterns)
    if dump is None:
        print("Wave slice: no dump.fst found", file=sys.stderr)
        return 0

    slices_dir = reports_dir / "slices"
    slices_dir.mkdir(parents=True, exist_ok=True)

    timestamp = int(time.time())
    base = re.sub(r"[^A-Za-z0-9_]+", "_", args.label.strip()) or "failure"
    out_fst = slices_dir / f"{base}_{timestamp}.fst"
    out_gtkw = slices_dir / f"{base}_{timestamp}.gtkw"
    out_png = slices_dir / f"{base}_{timestamp}.png"

    shutil.copy(dump, out_fst)

    start = max(0, fail_time - 200)
    stop = max(start + 1, fail_time + 200)
    gtkw_content = (
        f"$dumpfile {out_fst.as_posix()}\n"
        f"[timestart] {start}\n"
        f"[timestop] {stop}\n"
    )
    out_gtkw.write_text(gtkw_content)

    # Emit a tiny placeholder PNG (1x1 pixel) so dashboards can link to something.
    with out_png.open("wb") as png:
        png.write(
            bytes(
                [
                    0x89,
                    0x50,
                    0x4E,
                    0x47,
                    0x0D,
                    0x0A,
                    0x1A,
                    0x0A,
                    0x00,
                    0x00,
                    0x00,
                    0x0D,
                    0x49,
                    0x48,
                    0x44,
                    0x52,
                    0x00,
                    0x00,
                    0x00,
                    0x01,
                    0x00,
                    0x00,
                    0x00,
                    0x01,
                    0x08,
                    0x02,
                    0x00,
                    0x00,
                    0x00,
                    0x90,
                    0x77,
                    0x53,
                    0xDE,
                    0x00,
                    0x00,
                    0x00,
                    0x0A,
                    0x49,
                    0x44,
                    0x41,
                    0x54,
                    0x08,
                    0xD7,
                    0x63,
                    0xF8,
                    0xFF,
                    0xFF,
                    0x3F,
                    0x00,
                    0x05,
                    0xFE,
                    0x02,
                    0xFE,
                    0xA7,
                    0x61,
                    0x69,
                    0x83,
                    0x00,
                    0x00,
                    0x00,
                    0x00,
                    0x49,
                    0x45,
                    0x4E,
                    0x44,
                    0xAE,
                    0x42,
                    0x60,
                    0x82,
                ]
            )
        )

    print(f"Wave slice: {out_png.as_posix()} (FST: {out_fst.as_posix()})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
