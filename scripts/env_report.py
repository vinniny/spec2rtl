#!/usr/bin/env python3
"""Emit tool version information as JSON for build artifacts."""
from __future__ import annotations

import argparse
import json
import pathlib
import platform
import subprocess
from datetime import datetime, timezone
from typing import Any, Dict, Final, Tuple

WRAPPER = pathlib.Path(__file__).resolve().parents[1] / "tools" / "yosys-sv"

COMMANDS: Final[dict[str, str]] = {
    "verilator": "verilator --version",
    "verible": "verible-verilog-lint --version",
}


def capture_version(command: str) -> str:
    try:
        output = subprocess.check_output(command, shell=True, text=True, stderr=subprocess.STDOUT)
    except Exception:
        return "n/a"
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    return lines[0] if lines else "n/a"


def detect_yosys() -> Tuple[str, bool]:
    if not WRAPPER.exists():
        return "n/a", False
    try:
        output = subprocess.check_output([str(WRAPPER), "-V"], text=True, stderr=subprocess.STDOUT)
        version = output.splitlines()[0].strip() if output else "n/a"
    except Exception:
        version = "n/a"

    try:
        subprocess.check_call([str(WRAPPER), "-Q", "-p", "help read_systemverilog"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        plugin = True
    except Exception:
        plugin = False
    return version, plugin


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Capture tool versions")
    parser.add_argument("--out", type=pathlib.Path, default=pathlib.Path("reports/env.json"))
    parser.add_argument("--manifest", type=pathlib.Path)
    return parser.parse_args()


def update_manifest(manifest_path: pathlib.Path, yosys_version: str, uhdm: bool) -> None:
    data: Dict[str, Any]
    if manifest_path.exists():
        try:
            data = json.loads(manifest_path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            data = {"schema": 1}
    else:
        data = {"schema": 1}

    data["yosys"] = yosys_version
    data["uhdm_used"] = uhdm

    tools = data.setdefault("tools", {})
    if isinstance(tools, dict):
        tools["yosys"] = yosys_version
        tools["uhdm"] = uhdm
    else:
        data["tools"] = {"yosys": yosys_version, "uhdm": uhdm}

    synthesis = data.setdefault("synthesis", {})
    if isinstance(synthesis, dict):
        synthesis["uhdm_used"] = uhdm
    else:
        data["synthesis"] = {"uhdm_used": uhdm}

    manifest_path.parent.mkdir(parents=True, exist_ok=True)
    manifest_path.write_text(json.dumps(data, indent=2), encoding="utf-8")
    print(f"Updated manifest {manifest_path}")


def main() -> None:
    args = parse_args()
    versions = {tool: capture_version(cmd) for tool, cmd in COMMANDS.items()}
    yosys_version, plugin = detect_yosys()
    versions["yosys"] = yosys_version
    versions["uhdm"] = plugin

    manifest_path = args.manifest if args.manifest else args.out.parent / "run_manifest.json"
    update_manifest(manifest_path, yosys_version, plugin)

    payload = {
        "schema": 1,
        "captured_at_utc": datetime.now(timezone.utc).isoformat().replace("+00:00", "Z"),
        "host": platform.node(),
        "python": platform.python_version(),
        "tools": versions,
    }

    out_path = args.out
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
