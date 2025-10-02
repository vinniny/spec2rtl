# Claude Synthesis Memory

- Target flow: Yosys UHDM front-end via `tools/yosys-sv` running `synth/synth.ys`.
- Goal: zero inferred latches; prefer one-hot muxing over incomplete case statements.
- Preserve existing gate count unless spec requires functional change; suggest tweaks that keep adders registered.
- When latches appear, inspect `synth/yosys.log` around `Warning: Found latch` and propose missing default assignments.
- Example fix:
```systemverilog
always_comb begin
  sum_d = '0;      // default stops latch
  if (do_add) sum_d = a + b;
end
```
