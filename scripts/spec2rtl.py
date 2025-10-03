#!/usr/bin/env python3
"""Generate a SystemVerilog skeleton from docs/spec.md."""
from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import List


@dataclass
class Parameter:
    name: str
    default: str
    description: str


@dataclass
class Port:
    name: str
    direction: str
    width: str
    description: str


@dataclass
class Specification:
    module: str = "top"
    clock: str = "clk"
    reset: str = "rst_n"
    description: str = ""
    parameters: List[Parameter] | None = None
    ports: List[Port] | None = None
    requirements: List[str] | None = None


MARKDOWN_DIVIDER = set("-: ")
IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
REQ_LINE_RE = re.compile(r"^[-*]\s*\[[^\]]+]\s*(?:\([^\)]*\))?\s*(?P<text>.+)$")


def _extract_identifier(value: str) -> str:
    match = IDENT_RE.search(value)
    return match.group(0) if match else value.strip()


def parse_markdown_table(lines: List[str], start: int) -> tuple[List[List[str]], int]:
    table: List[List[str]] = []
    idx = start
    while idx < len(lines):
        line = lines[idx].strip()
        if not line.startswith("|"):
            break
        if set(line.replace("|", "")) <= MARKDOWN_DIVIDER:
            idx += 1
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        table.append(cells)
        idx += 1
    return table, idx


def parse_spec(path: Path) -> Specification:
    spec = Specification(parameters=[], ports=[], requirements=[])
    lines = path.read_text(encoding="utf-8").splitlines()
    idx = 0
    section: str | None = None

    while idx < len(lines):
        line = lines[idx].strip()
        lower = line.lower()
        if lower.startswith("- module:"):
            spec.module = _extract_identifier(line.split(":", 1)[1])
        elif lower.startswith("- clock:"):
            spec.clock = _extract_identifier(line.split(":", 1)[1])
        elif lower.startswith("- reset:"):
            spec.reset = _extract_identifier(line.split(":", 1)[1])
        elif lower.startswith("- description:"):
            spec.description = line.split(":", 1)[1].strip()
        elif lower.startswith("## parameters"):
            section = "parameters"
        elif lower.startswith("## interface"):
            section = "interface"
        elif lower.startswith("## requirements"):
            section = "requirements"
        elif section == "parameters" and line.startswith("|"):
            table, idx = parse_markdown_table(lines, idx)
            if table:
                header, *rows = table
                for row in rows:
                    if not row:
                        continue
                    name = row[0]
                    default = row[1] if len(row) > 1 else ""
                    desc = row[2] if len(row) > 2 else ""
                    if name:
                        spec.parameters.append(Parameter(name, default, desc))
            section = None
            continue  # we already advanced idx inside parse_markdown_table
        elif section == "interface" and line.startswith("|"):
            table, idx = parse_markdown_table(lines, idx)
            if table:
                header, *rows = table
                for row in rows:
                    if len(row) < 3:
                        continue
                    name, direction, width = row[:3]
                    desc = row[3] if len(row) > 3 else ""
                    if name:
                        spec.ports.append(Port(name, direction.lower(), width, desc))
            section = None
            continue
        elif section == "requirements" and line.startswith(("- ", "* ")):
            match = REQ_LINE_RE.match(line)
            if match:
                summary = match.group("text").strip()
                if summary:
                    spec.requirements.append(summary)
        idx += 1

    return spec


def width_decl(width: str) -> str:
    width = width.strip()
    if not width or width == "1":
        return ""
    if width.isdigit():
        return f"[{int(width) - 1}:0] "
    return f"[{width}-1:0] "


def format_port(port: Port, is_last: bool) -> str:
    direction = port.direction
    if direction not in {"input", "output", "inout"}:
        direction = "input"
    width = width_decl(port.width)
    comment = f"  // {port.description}" if port.description else ""
    suffix = "," if not is_last else ""
    return f"  {direction:6} logic {width}{port.name}{suffix}{comment}"


def render_module(spec: Specification) -> str:
    parameters = spec.parameters or []
    ports = spec.ports or []
    requirements = spec.requirements or []

    if not ports:
        raise SystemExit("Spec does not define any interface ports")

    port_lines = [format_port(port, idx == len(ports) - 1) for idx, port in enumerate(ports)]

    param_block = ""
    if parameters:
        entries = []
        for param in parameters:
            default = param.default or "'0"
            comment = f"  // {param.description}" if param.description else ""
            entries.append(f"  parameter {param.name} = {default},{comment}")
        entries[-1] = entries[-1].rstrip(",")
        param_block = "#(\n" + "\n".join(entries) + "\n) "

    requirement_lines = [f"// - {req}" for req in requirements] or ["// (no explicit requirements listed)"]

    output_ports = [p for p in ports if p.direction == "output"]
    assign_lines = [f"  assign {port.name} = '0;  // TODO" for port in output_ports]

    lines = [
        "`default_nettype none",
        f"module {spec.module} {param_block}(",
        *port_lines,
        ");",
        "",
        "// ------------------------------------------------------------------",
        "// Generated from docs/spec.md. Requirements summary:",
        *requirement_lines,
        "// ------------------------------------------------------------------",
        "",
        "// TODO: Implement the behaviour described by the requirements above.",
        *assign_lines,
        "endmodule",
        "`default_nettype wire",
        "",
    ]

    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate RTL skeleton from spec")
    parser.add_argument("--spec", default=Path("docs/spec.md"), type=Path)
    parser.add_argument("--rtl-dir", default=Path("rtl"), type=Path)
    args = parser.parse_args()

    spec = parse_spec(args.spec)
    args.rtl_dir.mkdir(parents=True, exist_ok=True)
    out_path = args.rtl_dir / f"{spec.module}.sv"
    out_path.write_text(render_module(spec) + "\n", encoding="utf-8")
    print(f"Wrote {out_path}")


if __name__ == "__main__":
    main()
