#!/usr/bin/env python3
"""Emit tool version information as JSON for build artifacts."""
from __future__ import annotations

import json
import subprocess
from typing import Final

COMMANDS: Final[dict[str, str]] = {
    "verilator": "verilator --version",
    "yosys": "./tools/yosys-sv -V | head -n1",
    "verible": "verible-verilog-lint --version",
}


def capture_version(command: str) -> str:
    try:
        output = subprocess.check_output(command, shell=True, text=True, stderr=subprocess.STDOUT)
    except Exception:
        return "n/a"
    lines = [line.strip() for line in output.splitlines() if line.strip()]
    return lines[0] if lines else "n/a"


def main() -> None:
    versions = {tool: capture_version(cmd) for tool, cmd in COMMANDS.items()}
    print(json.dumps(versions, indent=2))


if __name__ == "__main__":
    main()
