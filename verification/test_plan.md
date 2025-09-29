# Test Plan

- **R1**: shall register the sum of `a + b` into `y` on each rising edge of `clk`.
  - Directed stimulus: [{"a": 0, "b": 0}, {"a": 255, "b": 1}, {"a": 170, "b": 85}]
  - Random stimulus: {"count": 64, "constraints": {"a": [0, 255], "b": [0, 255]}}

- **R2**: shall drive `y` to zero when `rst_n` is asserted low.
  - Directed stimulus: [{"sequence": "rst_n low for 2 cycles, release, observe y"}]
  - Random stimulus: TBD

- **R3**: must treat additions modulo 256 (wrap on overflow).
  - Directed stimulus: [{"a": 0, "b": 0}, {"a": 255, "b": 1}, {"a": 170, "b": 85}]
  - Random stimulus: {"count": 64, "constraints": {"a": [0, 255], "b": [0, 255]}}
