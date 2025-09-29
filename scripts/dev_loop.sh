#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG_DIR="$ROOT_DIR/reports"
SEED_VALUE=${SEED:-}

if [[ -z "${VERILATOR:-}" && -x "$HOME/oss-cad-suite/bin/verilator" ]]; then
  export VERILATOR="$HOME/oss-cad-suite/bin/verilator"
fi

mkdir -p "$LOG_DIR"
cd "$ROOT_DIR"

make format
make lint

if [[ -n "$SEED_VALUE" ]]; then
  SEED_ARG="SEED=$SEED_VALUE"
else
  SEED_ARG=""
fi

if ! make check ${SEED_ARG}; then
  echo "Simulation failed; see reports/sim_report.json and reports/judge.json" >&2
  if [[ -f reports/judge.json ]]; then
    cat reports/judge.json >&2
  fi
  exit 1
fi

make synth

echo "Development loop completed successfully."
