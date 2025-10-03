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

- [R-RESET-001] (tags: reset; priority: must) All observable outputs shall drive zero while `rst_n` is asserted low and for one clock after deassertion.
- [R-FUNC-010] (tags: functional, arithmetic; priority: must) On every rising edge of `clk` with `rst_n` high, the design shall register `y = a + b`.
- [R-OVERFLOW-020] (tags: functional, overflow; priority: must) The addition must behave modulo 256, wrapping on overflow.
