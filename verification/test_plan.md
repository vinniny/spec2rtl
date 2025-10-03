# Test Plan

- **R-RESET-001** (must; tags: reset): All observable outputs shall drive zero while `rst_n` is asserted low and for one clock after deassertion.
  - Directed stimulus: [{"sequence": "drive rst_n low for 2 cycles, release, observe outputs"}]
  - Random stimulus: TBD

- **R-FUNC-010** (must; tags: arithmetic, functional): On every rising edge of `clk` with `rst_n` high, the design shall register `y = a + b`.
  - Directed stimulus: TBD
  - Random stimulus: TBD

- **R-OVERFLOW-020** (must; tags: functional, overflow): The addition must behave modulo 256, wrapping on overflow.
  - Directed stimulus: [{"a": 0, "b": 0}, {"a": 255, "b": 1}, {"a": 170, "b": 85}]
  - Random stimulus: {"count": 128, "constraints": {"a": [0, 255], "b": [0, 255]}}
