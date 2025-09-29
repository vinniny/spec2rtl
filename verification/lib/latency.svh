`ifndef VERIFICATION_LIB_LATENCY_SVH
`define VERIFICATION_LIB_LATENCY_SVH

`define SVA_LATENCY(NAME, TRIG, COND, MIN, MAX) \
  property NAME; \
    @(posedge clk) disable iff(!rst_n) (TRIG) |-> ##[MIN:MAX] (COND); \
  endproperty \
  assert property (NAME);

`endif
