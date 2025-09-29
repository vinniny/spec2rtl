`ifndef VERIFICATION_LIB_ONEHOT_SVH
`define VERIFICATION_LIB_ONEHOT_SVH

`define SVA_ONEHOT(NAME, SIG) \
`ifdef FORMAL \
  always @(posedge clk) begin : NAME``_onehot \
    if (rst_n) assert ($onehot0(SIG)); \
  end \
`else \
  NAME: assert property (@(posedge clk) disable iff(!rst_n) $onehot0(SIG)); \
`endif

`endif
