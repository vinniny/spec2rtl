# Contributing to spec2rtl

Thanks for considering a contribution! This checklist keeps the template healthy and predictable.

## Development flow
1. Create a Python virtual environment and install dependencies:
   ```bash
   python3 -m venv .venv
   source .venv/bin/activate
   pip install -r requirements.lock  # falls back to requirements.txt if needed
   ```
2. Run the deterministic smoke to regenerate assets and enforce gates:
   ```bash
   REPORTS_DIR=reports/_smoke SEED=1 make quick
   ```
3. Stage regenerated files (`verification/*`, `reports/_smoke/*`, etc.) alongside your source edits.

## Coding style & quality
- SystemVerilog: keep formatting/lint clean with `make lint` (Verible + Verilator).
- Python: run `pyflakes` (automatically invoked during `make quick`) and keep imports sorted.
- Commit regenerated artifacts (`verification/reqs.yml`, coverage JSON, dashboards) so reviewers see the evidence.

## Commit hygiene
- One logical change per commit when feasible; include regenerated artifacts in the same patch.
- Use imperative commit messages (e.g., “Add reset timing assertion”).
- Run `make quick` before opening a pull request; CI mirrors the same flow and will block if gates fail.

Happy hacking!
