# Verification Assertion Library

This directory hosts reusable assertion macros keyed off requirement tags. All macros assume a common clock/reset naming scheme of `clk` and `rst_n` unless otherwise documented.

## Base macros

- `` `include "lib/base.svh" `` provides shared helpers:
  - `` `REQ_VALID_STABLE_UNTIL_READY(valid, ready) `` — ensure `valid` holds high until `ready`.
  - `` `REQ_ONEHOT(vec) `` — ensure at most one bit in `vec` is asserted (`$onehot0`).

## Tag mapping

| Tag        | Include file              | Notes |
| ---------- | ------------------------- | ----- |
| `reset`    | `lib/reset.svh`           | Synchronous active-low reset checks using `clk`/`rst_n`. |
| `handshake`| `lib/handshake.svh`       | Ready/valid handshake macros. |
| `onehot`   | `lib/onehot.svh`          | One-hot encodings; also see base macro for quick checks. |
| `gray`     | `lib/gray_counter.svh`    | Gray code transition properties. |
| `latency`  | `lib/latency.svh`         | Bounded latency windows via `##[min:max]`. |

Add new tags by committing a small macro in `base.svh` or a sibling include, then updating this table and the tag mapper in `scripts/spec2tests.py`.
