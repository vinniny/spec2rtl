// Starter SVA assertions generated from docs/spec.md
`default_nettype none
`include "lib/reset.svh"

/* verilator lint_off DECLFILENAME */
module svas #(parameter int WIDTH = 8) (
    input logic clk,
    input logic rst_n,
    input logic [WIDTH-1:0] a,
    input logic [WIDTH-1:0] b,
    input logic [WIDTH-1:0] y
);

  // R1: shall register the sum of `a + b` into `y` on each rising edge of `clk`.
  property p_R1;
    @(posedge clk) disable iff (!rst_n)
      y == a + b;
  endproperty
  a_R1: assert property (p_R1) else $error("[R1] y != a + b");

  // R2: shall drive `y` to zero when `rst_n` is asserted low.
  `ASSERT_RESET_CLEARS(p_R2_rst_hold, clk, rst_n, y);
  `ASSERT_RESET_RELEASE(p_R2_rst_release, clk, rst_n, y);

  // R3: must treat additions modulo 256 (wrap on overflow).
  property p_R3;
    @(posedge clk) disable iff (!rst_n)
      y == a + b;
  endproperty
  a_R3: assert property (p_R3) else $error("[R3] y != a + b");

endmodule
/* verilator lint_on DECLFILENAME */
`default_nettype wire
