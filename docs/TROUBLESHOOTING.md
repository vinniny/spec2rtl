# Troubleshooting

Use this grab bag to unblock the template quickly.

- **Formal shows `ERROR 16` in `make formal_core`**
  - SymbiYosys could not spawn a solver. Install boa-friendly tools such as `boolector` or `z3` (OSS-CAD-Suite bundles both). Re-run and inspect `reports/formal/*/run.log` for details; the formal driver now prints the last 20 log lines on failure.
  - If you simply want to continue while you debug, run `make formal_soft` to record results without failing the build.

- **Synthesis complains about missing UHDM plugin**
  - The guard fires when `tools/yosys-sv` lacks `read_systemverilog`. Either install an UHDM-enabled Yosys (OSS-CAD-Suite) or rely on the built-in fallback, which now runs plain `yosys` with `read_verilog -sv` and still produces `synth/yosys.log` + `reports/synth_report.json`.

- **UHDM / `read_systemverilog` not found**
  - Verify the plugin with:
    ```bash
    ./tools/yosys-sv -Q -p "help read_systemverilog"
    ```
  - If the command still fails, check whether `systemverilog.so` is present under your suite (for example `oss-cad-suite/share/yosys/plugins/systemverilog.so`). As a last resort:
    ```bash
    LD_LIBRARY_PATH=<suite>/lib ./tools/yosys-sv -Q -m <suite>/share/yosys/plugins/systemverilog.so -p "help read_systemverilog"
    ```
  - Once this command succeeds, `make synth` automatically loads the plugin.

- **Per-requirement coverage gates trip**
  - Check `reports/*/coverage_per_req.json` for the failing IDs. Edit `policies.yml` (see `coverage.per_req_overrides`) or add neutral hooks in your testbench (for example, call `cov_hit("ID")` after each requirement scenario) to raise coverage for that ID.

- **Simulation reports empty tests**
  - The harness now refuses to emit a report if zero tests ran. Check the testbench for early `$finish` or missing stimulus.

- **Mutation build errors**
  - Mutants reuse the same SVA set; if they fail to compile, look at `reports/mutation/<mutant>/` for the simulator log. Common causes are malformed IDs in generated SVAs—rerun `make spec` to regenerate after editing the spec.

- **CI tips**
  - Pin `SEED` in CI (`SEED=12345 make quick`) so random stimulus stays deterministic.
  - Use `REPORTS_DIR=reports/ci` to keep artifacts isolated, then upload the directory (HTML dashboard, JUnit XML, JSON) as a job artifact.
