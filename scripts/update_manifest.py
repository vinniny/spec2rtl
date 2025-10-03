#!/usr/bin/env python3
"""Update or create run_manifest.json with synthesis metadata."""
from __future__ import annotations

import argparse
import json
from pathlib import Path


def str_to_bool(value: str) -> bool:
    value = value.lower()
    if value in {"1", "true", "yes", "on"}:
        return True
    if value in {"0", "false", "no", "off"}:
        return False
    raise argparse.ArgumentTypeError(f"cannot interpret '{value}' as boolean")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Update synthesis manifest metadata")
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--yosys", type=str, default=None)
    parser.add_argument("--uhdm", type=str_to_bool, default=None)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    manifest_path = args.manifest

    data: dict[str, object]
    if manifest_path.exists():
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            data = {"schema": 1}
    else:
        data = {"schema": 1}

    if args.yosys is not None:
        data["yosys"] = args.yosys
    if args.uhdm is not None:
        data["uhdm_used"] = args.uhdm

    tools = data.setdefault("tools", {})
    if isinstance(tools, dict):
        if args.yosys is not None:
            tools["yosys"] = args.yosys
        if args.uhdm is not None:
            tools["uhdm"] = args.uhdm

    if args.uhdm is not None:
        synthesis = data.setdefault("synthesis", {})
        if isinstance(synthesis, dict):
            synthesis["uhdm_used"] = args.uhdm

    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Updated manifest {manifest_path}")


if __name__ == "__main__":
    main()
