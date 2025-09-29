`default_nettype none
`include "verification/lib/reset.svh"
`include "verification/lib/onehot.svh"
`include "verification/lib/gray_counter.svh"

module props #(
    parameter int WIDTH = 8,
    parameter bit ENABLE_RESET = 1,
    parameter bit ENABLE_TEMPORAL = 1,
    parameter bit ENABLE_ONEHOT = 0,
    parameter bit ENABLE_GRAY = 0
) (
    input  logic              clk,
    input  logic              rst_n,
    input  logic [WIDTH-1:0]  a,
    input  logic [WIDTH-1:0]  b,
    input  logic [WIDTH-1:0]  y,
    input  logic [WIDTH-1:0]  onehot_sig,
    input  logic [WIDTH-1:0]  gray_sig
);
  generate
    if (ENABLE_RESET) begin : g_reset
      `ASSERT_RESET_CLEARS(p_reset_hold, clk, rst_n, y);
      `ASSERT_RESET_RELEASE(p_reset_release, clk, rst_n, y);
    end

    if (ENABLE_TEMPORAL) begin : g_temporal
`ifdef FORMAL
      always @(posedge clk) begin : p_sum_latency_formal
        if ($past(rst_n)) assert (y == a + b);
      end
`else
      a_sum_latency: assert property (@(posedge clk) disable iff (!rst_n) y == a + b);
`endif
    end

    if (ENABLE_ONEHOT) begin : g_onehot
      `SVA_ONEHOT(p_onehot, onehot_sig);
    end

    if (ENABLE_GRAY) begin : g_gray
      `SVA_GRAY(p_gray, gray_sig);
    end
  endgenerate
endmodule
`default_nettype wire
