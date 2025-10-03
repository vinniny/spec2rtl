# Sample Arithmetic Unit Spec

This miniature spec demonstrates the expected Markdown structure.

- [R1] (tags: reset, must) Upon deasserting `rst_n`, `sum_q` shall reset to zero on the next rising edge of `clk`.
- [R2] (tags: addition, must) The DUT shall drive `sum_q` with the unsigned sum of inputs `a` and `b` each cycle.
- [R3] (tags: overflow, should) When the addition overflows 8 bits, `sum_q` shall saturate at `8'hFF`.

> Copy this file when you start a new project, edit the requirement text, and run `make spec2tests` to generate the verification artifacts.
