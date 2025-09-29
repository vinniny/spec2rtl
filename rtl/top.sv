`default_nettype none
module top (
    input  logic       clk,
    input  logic       rst_n,
    input  logic [7:0] a,
    input  logic [7:0] b,
    output logic [7:0] y
);
  logic [7:0] sum_q, sum_d;

  always_comb begin
    sum_d = a + b;
  end

  always_ff @(posedge clk) begin
    if (!rst_n) sum_q <= '0;
    else sum_q <= sum_d;
  end

  assign y = sum_q;
endmodule
`default_nettype wire
