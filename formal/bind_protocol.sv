`default_nettype none

// Update the signal hookups as protocol-facing nets become available in the DUT.
bind top props #(
    .WIDTH(8),
    .ENABLE_RESET(1),
    .ENABLE_TEMPORAL(1),
    .ENABLE_ONEHOT(1),
    .ENABLE_GRAY(1)
) u_props_protocol (
    .clk       (clk),
    .rst_n     (rst_n),
    .a         (a),
    .b         (b),
    .y         (y),
    .onehot_sig('0),
    .gray_sig  ('0)
);

`default_nettype wire
