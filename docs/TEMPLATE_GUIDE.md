# Template Guide

This repository is a template for turning a Markdown spec into verification and implementation assets. Use this checklist when you clone the template into a new project.

## Inputs
- `docs/spec.md`: capture requirements as markdown bullets using the canonical form `- [REQ-ID] (tags: tag1, tag2; priority: must) Requirement text with shall/must language.`
- Optional reusable context lives under `docs/context/*.md`. Store interface conventions, reset styles, or policy notes you want to share across projects.
- `policies.yml`: tune quality gates for lint, coverage, formal, mutation, and synthesis. The defaults are conservative; adjust thresholds per design.

## Commands
Run `make help` to list the common entry points. Typical flow:
1. `make quick` — generate verification assets, lint the codebase, then run simulation, coverage, and judge.
2. `make all` — quick flow plus synthesis, formal, mutation testing, and dashboards.
3. Individual stages: `make env spec lint report synth formal_core mutate dashboards`.
4. Developer smoke test: `make smoke` runs the quick flow with `REPORTS_DIR=reports/_smoke` and a fixed seed.

Pass `SEED=<value>` to make to fix stimulus determinism. In CI, pin the seed; locally you can omit it to use a random value.

## Outputs
Generated artifacts are kept under version control friendly directories:
- `verification/reqs.yml`, `verification/test_plan.md`, `verification/svas.sv`
- `reports/env.json`, `reports/run_manifest.json`, `reports/sim_report.json`, `reports/coverage.json`, `reports/coverage_per_req.json`, `reports/judge.json`, `reports/junit.xml`
- `reports/dashboard.{md,html}`, `reports/site/` (publishable dashboard)
- `synth/out.json`, `synth/yosys.log`
- `formal/<profile>/PASS` (or failure artifacts)
- `mutants/` when mutation testing is executed
- `docs/TROUBLESHOOTING.md` collects quick fixes for common setup issues

Clean everything with `make clean`; add `make distclean` to remove formal traces and synthesis logs as well.

## Raising or Lowering Gates
Edit `policies.yml` to update thresholds. For example:
```yaml
coverage:
  line: 90
  toggle: 85
```
Scripts such as `check_gates.py`, `yosys_to_json.py`, and `run_formal.py` read this file to decide pass/fail criteria. Commit changes alongside the spec update so reviewers can see the new acceptance bar.

## Extending Tags and Assertions
Tag-to-assertion mappings live in `scripts/spec2tests.py` and `verification/lib/*.svh`. To add a new requirement tag:
1. Define a reusable macro in `verification/lib/base.svh` or another library include.
2. Document the macro usage in `verification/lib/README.md`.
3. Extend the tag map in `scripts/spec2tests.py` so requirements with the new tag include the appropriate assertions.

Keep macros clock/reset agnostic by relying on the common `(clk, rst_n)` naming. Document any assumptions in the library README so downstream projects do not guess.
