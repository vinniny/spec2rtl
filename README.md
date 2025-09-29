# spec2rtl

**From spec → RTL → verification → synthesis with reproducible, requirement-aware automation.**

```
Spec (Markdown)
      │
      ▼
Spec2Tests → Tests & SVAs → Simulation + Coverage → Judge → Synthesis → Reports
                        │
                        └── Formal & Mutation Guards
```

## Repository Layout
- `rtl/` – synthesizable RTL designs (designs under test).
- `tb/` – requirement-aware testbenches with coverage bins and requirement IDs.
- `verification/` – generated `reqs.yml`, `test_plan.md`, `svas.sv`, plus reusable assertion macros under `verification/lib/`.
- `formal/` – formal properties, bind wrappers, and SymbiYosys configurations.
- `synth/` – Yosys UHDM scripts, logs, and synthesis JSON outputs.
- `scripts/` – automation utilities (`spec2tests.py`, `judge.py`, coverage converters, mutation tools, etc.).
- `reports/` – generated artifacts (`sim_report.json`, `coverage.json`, dashboards, traces, badges).
- `tools/` – third-party wrappers and helper binaries (yosys-sv, verible, REST API server).
- `.github/workflows/` – GitHub Actions pipeline definitions.

## Environment Setup
1. **Host OS** – Ubuntu 22.04 LTS (bare metal) or Windows 11 + WSL2. Other Linux distributions work if they provide the same toolchain.

2. **Package prerequisites**
   ```bash
   sudo apt update
   sudo apt install build-essential python3 python3-venv python3-pip git
   sudo apt install verilator symbiyosys gtkwave   # gtkwave optional but useful
   ```
   For SystemVerilog synthesis use either:
   - **OSS CAD Suite** (recommended) – download the latest bundle with UHDM-enabled Yosys.
   - **Yosys + Surelog/UHDM** – build from source if you prefer.

3. **Verible**
   - The repository ships a pinned build under `tools/verible/` that is used automatically.
   - Alternatively install a newer release and update `PATH` if desired.

4. **Python virtual environment**
   ```bash
   python3 -m venv .venv
   source .venv/bin/activate
   pip install --upgrade pip
   pip install -r requirements.txt
   ```

5. **Toolchain smoke test**
   ```bash
   make env
   cat reports/env.json
   ```
   This records the versions that CI expects to see. Address any `n/a` entries before running the full flow.

## Workflow Overview

### 1. Describe the design (`docs/spec.md`)
Requirements are written in Markdown using “shall/must” language. Each bullet becomes a tracked requirement with unique ID (`R1`, `R2`, …).

### 2. Generate verification collateral (Spec2Tests)
`python3 scripts/spec2tests.py` or `make spec2tests`
- Produces `verification/reqs.yml`, `test_plan.md`, and `svas.sv`.
- Copies any hand-authored signal maps or timing windows for SVAs (e.g., handshake latency) from existing YAML entries.
- Pulls reusable macros from `verification/lib/` so assertions are added by tag rather than rewriting SV code.

### 3. Lint
`make lint`
- Runs Verible formatter/linter and Verilator lint-only compile.
- Enforces coding style and catches obvious SV mistakes before simulation.

### 4. Simulate & collect coverage
`make report`
- Builds the Verilator testbench, runs seeded regression (`SIM_ARGS`), and stores console output in `reports/sim.log`.
- Converts results into machine-readable JSON (`sim_report.json`) with requirement IDs, pass/fail counts, and coverage samples.
- Extracts coverage (line/toggle/bin) via `coverage_to_json.py` and `coverage_per_req.py`.

### 5. Judge failures
`scripts/judge.py` (invoked by `make report`)
- Categorises failures into reset, signedness, handshake, latency, width, etc.
- Emits `reports/judge.json` with actionable hints and a triage tag that is reused by automation (e.g., draft patch suggestions).

### 6. Synthesize
`make synth`
- Runs Yosys (UHDM front-end) to produce JSON netlists and logs.
- Fails if latches are inferred; details appear in `reports/synth_report.json`.

### 7. Formal proof
`make formal_all`
- Executes SymbiYosys on `formal/top.sby` (reset/temporal properties) and `formal/top_protocol.sby` (optional one-hot / gray-code checks).
- Assertions are bound into the DUT via `formal/bind_*.sv` so RTL wiring stays untouched.

### 8. Mutation testing
`make mutate`
- Automatically edits `rtl/top.sv` with typical bug patterns (off-by-one, signedness, dropped reset, etc.).
- The regression must fail with the mutant to prove tests are sensitive. Survivors cause the Make target to error out.

### 9. Dashboards & badge
`make dashboards` / `make badge`
- Generates Markdown + HTML dashboards (`reports/dashboard.md`, `reports/dashboard.html`, `reports/site/index.html`).
- Updates `reports/coverage_badge.svg`, which is referenced at the top of this README.

### 10. CI/CD
- `.github/workflows/ci.yml` runs the sequence: lint → check (sim + coverage gates) → synth → formal_all → dashboards/badge → junit/artifact upload.
- Reports are preserved as workflow artifacts so teammates can download results without rerunning locally.

## Daily Workflow (Make targets)

| Command | When to run | What it does |
| --- | --- | --- |
| `make spec2tests` | After editing the Markdown spec | Regenerates requirements, test plan, and SVAs, preserving manual maps/params. |
| `make lint` | Before committing | Runs Verible + Verilator to guarantee style and lint cleanliness. |
| `make report` | During development, before reviews | Builds + runs the simulation, generates JSON reports, updates judge/coverage files. |
| `make cov_summarize` | After new coverage data is available | Converts LCOV to JSON summaries consumed by dashboards and coverage gates. |
| `make trace_md` | When you need a human-readable trace snapshot | Produces `reports/trace.md` linked to requirements. |
| `make check` | Pre-merge gate | Re-runs report + coverage summaries and enforces global/per-requirement thresholds. |
| `make synth` | Whenever RTL changes | Ensures Yosys can synthesize the DUT without latches or width mismatches. |
| `make formal_all` | When changing reset/handshake/encoding logic | Runs all SymbiYosys proofs (base + protocol binds). |
| `make mutate` | Before sign-off | Confirms the testbench kills common bug patterns (surviving mutants indicate missing checks). |
| `make dashboards` | Before sharing results | Updates HTML/Markdown dashboards, including `reports/site/index.html` for GitHub Pages. |
| `make badge` | After coverage improvements | Refreshes the coverage badge embedded in the README. |

## Reports & Artifacts
- **`reports/sim_report.json`** – simulation schema output with status, requirement sample counts, seed, and signature hash.
- **`reports/judge.json`** – triage decision (`triage`, `hint`, `action`) for automation and code review hand-off.
- **`reports/coverage.json` / `reports/coverage_per_req.json`** – aggregated coverage metrics (line/toggle/bin) plus per-requirement breakdowns.
- **`reports/trace.json` / `reports/trace.md`** – requirement traceability matrix in JSON/Markdown.
- **`reports/synth_report.json`** – synthesis summary indicating latch detection, cell counts, warnings.
- **`reports/formal.log`** – transcript of SymbiYosys runs covering both default and protocol bind tasks.
- **`reports/patch.diff`** – draft patch from `scripts/draft_patch.py` based on judge triage.
- **`reports/coverage_badge.svg`** – auto-generated coverage badge referenced in the README.
- **`reports/dashboard.md` / `reports/dashboard.html` / `reports/site/index.html`** – dashboard snapshots ready for sharing or GitHub Pages.
- **`reports/junit.xml`** – JUnit-formatted report for CI consumption.

## CI/CD
GitHub Actions runs lint → check → synth → formal → dashboards/badge. Reports are uploaded as build artifacts and the coverage badge embedded in this README is refreshed automatically.

## Contribution Guidelines
- **Keep spec and artifacts in sync** – run `make spec2tests` whenever you touch `docs/spec.md`; commit the regenerated files under `verification/`.
- **Lint before you push** – `make lint` must pass (both Verible and Verilator).
- **Generated reports stay out of git** – everything under `reports/` is transient; rely on CI artifacts instead.
- **Mutation-sensitive tests** – `make mutate` should fail any injected bug. Add assertions, coverage bins, or directed tests if a mutant survives.
- **Extending the taxonomy** – new requirement tags should come with matching macros in `verification/lib/` and updates to `scripts/spec2tests.py` (maps/params) so automation can wire them automatically.
