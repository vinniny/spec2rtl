#!/usr/bin/env python3
"""Generate a suggested patch based on judge diagnostics (preview only)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

JUDGE_PATH = Path("reports/judge.json")
PATCH_PATH = Path("reports/patch.diff")

RESET_PATCH = [
    "--- a/rtl/top.sv",
    "+++ b/rtl/top.sv",
    "@@",
    " always_ff @(posedge clk) begin",
    "-  // TODO",
    "+  if (!rst_n) y <= '0; else y <= a + b;",
    " end",
]

UNSIGNED_EXT_PATCH = [
    "--- a/rtl/top.sv",
    "+++ b/rtl/top.sv",
    "@@",
    "-  always_comb begin",
    "-    sum_d = a + b;",
    "-  end",
    "+  logic [8:0] tmp;",
    "+",
    "+  always_comb begin",
    "+    tmp   = {1'b0, a} + {1'b0, b};",
    "+    sum_d = tmp[7:0];",
    "+  end",
    "+",
    "+  // carry propagates through tmp[8]; expose it via coverage or status bits as needed",
]

SIGNED_PATCH = [
    "--- a/rtl/top.sv",
    "+++ b/rtl/top.sv",
    "@@",
    "-  logic [7:0] sum_q, sum_d;",
    "+  logic [7:0] sum_q, sum_d;",
    "+  logic signed [8:0] sa, sb, sz;",
    "@@",
    "-  always_comb begin",
    "-    sum_d = a + b;",
    "-  end",
    "+  always_comb begin",
    "+    sa    = $signed({1'b0, a});",
    "+    sb    = $signed({1'b0, b});",
    "+    sz    = sa + sb;",
    "+    sum_d = sz[7:0];",
    "+  end",
]

REGCOMB_PATCH = [
    "--- a/rtl/top.sv",
    "+++ b/rtl/top.sv",
    "@@",
    "-  assign y = a + b;",
    "+  logic [7:0] y_q;",
    "+  always_ff @(posedge clk) begin",
    "+    if (!rst_n) y_q <= '0;",
    "+    else y_q <= a + b;",
    "+  end",
    "+  assign y = y_q;",
]

HANDSHAKE_PATCH = [
    "--- a/rtl/top.sv",
    "+++ b/rtl/top.sv",
    "@@",
    " module top (",
    "     input  logic       clk,",
    "     input  logic       rst_n,",
    "     input  logic [7:0] a,",
    "     input  logic [7:0] b,",
    "-    output logic [7:0] y",
    "+    output logic [7:0] y,",
    "+    input  logic        req_valid,",
    "+    output logic       req_ready,",
    "+    output logic       rsp_valid,",
    "+    input  logic       rsp_ready",
    " );",
    "@@",
    "-  assign y = sum_q;",
    "+  assign y = sum_q;",
    "+",
    "+  // Example ready/valid handshake skeleton",
    "+  always_ff @(posedge clk) begin",
    "+    if (!rst_n) begin",
    "+      req_ready <= 1'b0;",
    "+      rsp_valid <= 1'b0;",
    "+    end else begin",
    "+      req_ready <= !rsp_valid || rsp_ready;",
    "+      if (req_valid && req_ready) begin",
    "+        rsp_valid <= 1'b1;",
    "+        // TODO: latch payload here",
    "+      end else if (rsp_valid && rsp_ready) begin",
    "+        rsp_valid <= 1'b0;",
    "+      end",
    "+    end",
    "+  end",
]


def load_judge() -> dict[str, object]:
    if not JUDGE_PATH.exists():
        print(f"No judge report found at {JUDGE_PATH}", file=sys.stderr)
        sys.exit(1)

    try:
        return json.loads(JUDGE_PATH.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        print(f"Failed to parse {JUDGE_PATH}: {exc}", file=sys.stderr)
        sys.exit(1)


def select_patch(triage: str | None) -> list[str]:
    match (triage or "").lower():
        case "reset_path":
            return RESET_PATCH
        case "arith_width":
            return UNSIGNED_EXT_PATCH
        case "signedness":
            return SIGNED_PATCH
        case "reg_vs_comb":
            return REGCOMB_PATCH
        case "handshake":
            return HANDSHAKE_PATCH
        case _:
            return []


def main() -> None:
    judge = load_judge()
    triage = judge.get("triage")
    hint = judge.get("hint")

    patch_lines = select_patch(triage)
    if not patch_lines:
        print("No draft patch available for this triage; nothing written")
        if hint:
            print(f"Hint: {hint}")
        return

    PATCH_PATH.write_text("\n".join(patch_lines) + "\n", encoding="utf-8")
    print(f"{PATCH_PATH.as_posix()} written (preview only)")
    if hint:
        print(f"Hint: {hint}")


if __name__ == "__main__":
    main()
