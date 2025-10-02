# Claude Verification Memory

Judge taxonomy focus:
- Reset: check both clear (`rst_n == 0`) and release edges.
- Signedness: ensure arithmetic preserves unsigned 8-bit math; flag implicit sign extensions.
- Latency: outputs register exactly one cycle after inputs; no extra pipeline bubbles.
- Handshake: this design is free-running; avoid inventing ready/valid.
- Width: keep buses at 8 bits unless spec/reqs introduce wider data.

SVA helpers live in `verification/lib/reset.svh`:
```systemverilog
`ASSERT_RESET_CLEARS(NAME, CLK, RST_N, SIG)
`ASSERT_RESET_RELEASE(NAME, CLK, RST_N, SIG)
```
Bind assertions rather than editing DUT ports. Example bind snippet:
```systemverilog
bind top svas #(.WIDTH(8)) u_svas (
  .clk(clk), .rst_n(rst_n), .a(a), .b(b), .y(y)
);
```
When proposing fixes, cite failing requirement IDs (R#) and low-coverage bins from `coverage_per_req.json`.
