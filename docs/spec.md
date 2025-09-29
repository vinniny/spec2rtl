# Registered 8-bit Adder (top)

- Module: top
- Clock: clk
- Reset: rst_n (active-low synchronous)
- Description: Adds operands `a` and `b`, registering result on the rising edge of `clk`.

## Parameters

| Name | Default | Description |
| ---- | ------- | ----------- |

## Interface

| Name  | Direction | Width | Description |
| ----- | --------- | ----- | ----------- |
| clk   | input     | 1     | System clock |
| rst_n | input     | 1     | Active-low synchronous reset |
| a     | input     | 8     | Operand A |
| b     | input     | 8     | Operand B |
| y     | output    | 8     | Registered sum |

## Requirements

- shall register the sum of `a + b` into `y` on each rising edge of `clk`.
- shall drive `y` to zero when `rst_n` is asserted low.
- must treat additions modulo 256 (wrap on overflow).
