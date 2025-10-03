// Starter SVA assertions generated from docs/spec.md
`default_nettype none
`include "lib/base.svh"
`include "lib/reset.svh"

/* verilator lint_off DECLFILENAME */
module svas #(parameter int WIDTH = 8) (
    input logic clk,
    input logic rst_n,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic [WIDTH-1:0] y
);

  // R-RESET-001: All observable outputs shall drive zero while `rst_n` is asserted low and for one clock after deassertion.
  `ASSERT_RESET_CLEARS(p_R_RESET_001_rst_hold, clk, rst_n, y);
  `ASSERT_RESET_RELEASE(p_R_RESET_001_rst_release, clk, rst_n, y);

  // R-FUNC-010: On every rising edge of `clk` with `rst_n` high, the design shall register `y = a + b`.
  property p_R_FUNC_010;
    @(posedge clk) disable iff (!rst_n)
      y == a + b;
  endproperty
  a_R_FUNC_010: assert property (p_R_FUNC_010) else $error("[R-FUNC-010] y != a + b");

  // R-OVERFLOW-020: The addition must behave modulo 256, wrapping on overflow.
  property p_R_OVERFLOW_020;
    @(posedge clk) disable iff (!rst_n)
      y == a + b;
  endproperty
  a_R_OVERFLOW_020: assert property (p_R_OVERFLOW_020) else $error("[R-OVERFLOW-020] y != a + b");

endmodule
/* verilator lint_on DECLFILENAME */
`default_nettype wire
