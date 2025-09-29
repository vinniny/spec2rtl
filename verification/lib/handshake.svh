`ifndef VERIFICATION_LIB_HANDSHAKE_SVH
`define VERIFICATION_LIB_HANDSHAKE_SVH

`define SVA_REQ_ACK(NAME, REQ, ACK, MIN, MAX) \
  property NAME; \
    @(posedge clk) disable iff(!rst_n) (REQ) |-> ##[MIN:MAX] (ACK); \
  endproperty \
  assert property (NAME);

`endif
