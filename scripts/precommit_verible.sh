#!/bin/bash
set -euo pipefail
ROOT="$(git rev-parse --show-toplevel)"
FORMAT="$ROOT/tools/verible/bin/verible-verilog-format"
LINT="$ROOT/tools/verible/bin/verible-verilog-lint"
if [ ! -x "$FORMAT" ] || [ ! -x "$LINT" ]; then
  exit 0
fi
if [ "$#" -eq 0 ]; then
  exit 0
fi
"$FORMAT" --inplace "$@"
"$LINT" "$@"
