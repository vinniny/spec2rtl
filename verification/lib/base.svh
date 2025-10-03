`ifndef VERIFICATION_LIB_BASE_SVH
`define VERIFICATION_LIB_BASE_SVH

`define REQ_VALID_STABLE_UNTIL_READY(valid, ready) \
  assert property (@(posedge clk) disable iff(!rst_n) (valid && !ready) |=> valid)

`define REQ_ONEHOT(vec) \
  assert property (@(posedge clk) $onehot0(vec))

`endif
