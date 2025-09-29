`ifndef VERIFICATION_LIB_GRAY_COUNTER_SVH
`define VERIFICATION_LIB_GRAY_COUNTER_SVH

`define SVA_GRAY(NAME, SIG) \
`ifdef FORMAL \
  always @(posedge clk) begin : NAME``_gray \
    if (rst_n) assert ($countones(SIG ^ $past(SIG)) <= 1); \
  end \
`else \
  NAME: assert property (@(posedge clk) disable iff(!rst_n) $countones(SIG ^ $past(SIG)) <= 1); \
`endif

`endif
