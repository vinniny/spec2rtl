`default_nettype none

bind top props #(
    .WIDTH(8),
    .ENABLE_RESET(1),
    .ENABLE_TEMPORAL(1),
    .ENABLE_ONEHOT(0),
    .ENABLE_GRAY(0)
) u_props (
    .clk       (clk),
    .rst_n     (rst_n),
    .a         (a),
    .b         (b),
    .y         (y),
    .onehot_sig('0),
    .gray_sig  ('0)
);

`default_nettype wire
