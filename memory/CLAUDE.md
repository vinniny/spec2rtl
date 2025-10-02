# Claude Global Memory

- Reset policy: synchronous, active-low `rst_n` that clears state to `'0`. Keep sampling on `posedge clk` only.
- Style: always wrap RTL files with `` `default_nettype none`` / `` `default_nettype wire`` and prefer `logic` types.
- Determinism: surface any random seeds; default testbench uses `+seed=<int>` and expects reproducible re-runs.
- No inferred latches; drive every `always_comb` assignment for all paths.
- Prefer small, surgical diffs; keep published interfaces stable unless spec demands otherwise.

Good register stage:
```systemverilog
always_ff @(posedge clk) begin
  if (!rst_n) sum_q <= '0;
  else sum_q <= sum_d;
end
```

Bad (latch + async reset):
```systemverilog
always @(a or rst_n)
  if (!rst_n) sum_q = '0; // level-sensitive
  else if (enable) sum_q = a; // holds prior value when enable=0
```
