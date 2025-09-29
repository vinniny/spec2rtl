#!/usr/bin/env python3
"""Generate SVA scaffolding from docs/spec.md."""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPT_DIR))

from spec2rtl import Specification, parse_spec, width_decl  # type: ignore  # noqa: E402


def render_asserts(spec: Specification) -> str:
    ports = spec.ports or []
    if not ports:
        raise SystemExit("Spec does not define interface ports")

    port_lines = []
    for idx, port in enumerate(ports):
        width = width_decl(port.width)
        comment = f"  // {port.description}" if port.description else ""
        suffix = "," if idx < len(ports) - 1 else ""
        port_lines.append(f"  input logic {width}{port.name}{suffix}{comment}")

    requirements = spec.requirements or []
    if not requirements:
        requirements = ["Requirement placeholder"]

    property_blocks = []
    for idx, requirement in enumerate(requirements, start=1):
        prop_name = f"p_req_{idx:02d}"
        comment = f"// From spec: {requirement}"
        property_blocks.extend(
            [
                comment,
                f"property {prop_name};",
                f"  @(posedge {spec.clock}) disable iff (!{spec.reset})",
                "    // TODO: translate requirement into SVA",
                "    1'b1 |-> 1'b1;",
                "endproperty",
                f"a_{prop_name}: assert property ({prop_name});",
                "",
            ]
        )

    lines = [
        "`default_nettype none",
        f"module {spec.module}_asserts (",
        *port_lines,
        ");",
        "",
        "// verilator lint_off UNUSEDSIGNAL",
        "// Auto-generated placeholder assertions. Refine before use.",
        *property_blocks,
        "// verilator lint_on UNUSEDSIGNAL",
        "endmodule",
        "`default_nettype wire",
        "",
    ]
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate assertion scaffolding from spec")
    parser.add_argument("--spec", default=Path("docs/spec.md"), type=Path)
    parser.add_argument("--out", default=Path("tb/top_asserts.sv"), type=Path)
    args = parser.parse_args()

    spec = parse_spec(args.spec)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(render_asserts(spec) + "\n", encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
