`ifndef VERIFICATION_LIB_RESET_SVH
`define VERIFICATION_LIB_RESET_SVH

`define ASSERT_RESET_CLEARS(NAME, CLK, RST_N, SIG) \
`ifdef FORMAL \
  always @(posedge CLK) begin : NAME``_clr \
    if (!RST_N) assert (SIG == '0); \
  end \
`else \
  NAME: assert property (@(posedge CLK) (!RST_N) |-> (SIG == '0)) else $error("reset clear violation"); \
`endif

`define ASSERT_RESET_RELEASE(NAME, CLK, RST_N, SIG) \
`ifdef FORMAL \
  always @(posedge CLK) begin : NAME``_rel \
    if ($past(RST_N) === 1'b0 && RST_N) assert (SIG == '0); \
  end \
`else \
  NAME``_rel: assert property (@(posedge CLK) disable iff (!RST_N) $rose(RST_N) |-> (SIG == '0)) else $error("reset release violation"); \
`endif

`endif
