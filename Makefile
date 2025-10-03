VERIBLE_BIN := $(PWD)/tools/verible/bin
PATH := $(VERIBLE_BIN):$(PATH)
SHELL := /bin/bash

PYTHON ?= python3
VERILATOR ?= verilator
YOSYS_SV ?= ./tools/yosys-sv
SBY ?= sby

VERIBLE_FORMAT := $(VERIBLE_BIN)/verible-verilog-format
VERIBLE_LINT := $(VERIBLE_BIN)/verible-verilog-lint
VERIBLE_RULES ?= .verible.rules
VERIBLE_RULES_ARG := $(if $(wildcard $(VERIBLE_RULES)),--rules_config=$(VERIBLE_RULES))

TOP_TB ?= top_tb

# Deterministic default seed; override per run as needed.
SEED ?= 12345
SIM_ARGS := +seed=$(SEED)
FLAKE_RETRIES ?= 1

# RTL source selection (support mutant overrides)
RTL_FILES := $(abspath $(wildcard rtl/*.sv))
ifneq ($(strip $(MUTANT_SOURCE)),)
MUTANT_SOURCE_ABS := $(abspath $(MUTANT_SOURCE))
RTL_FILES := $(filter-out $(MUTANT_SOURCE_ABS),$(RTL_FILES))
endif
ifneq ($(strip $(MUTANT_RTL)),)
RTL_FILES += $(abspath $(MUTANT_RTL))
endif

TB_FILES := $(abspath $(filter-out tb/top_asserts.sv,$(wildcard tb/*.sv)))
VERIF_SV := $(abspath $(wildcard verification/*.sv))
SV_SOURCES := $(RTL_FILES) $(TB_FILES)

ifeq ($(origin REPORTS_DIR), undefined)
  ifneq ($(strip $(MUTANT_OUT)),)
    REPORTS_DIR := $(MUTANT_OUT)
  else
    REPORTS_DIR := reports
  endif
endif
REPORTS_DIR := $(abspath $(REPORTS_DIR))

BUILD_DIR := build/sim
SIM_BIN := $(BUILD_DIR)/obj_dir/V$(TOP_TB)
SIM_LOG := $(REPORTS_DIR)/sim.log
SIM_REPORT := $(REPORTS_DIR)/sim_report.json
ENV_JSON := $(REPORTS_DIR)/env.json
RUN_MANIFEST := $(REPORTS_DIR)/run_manifest.json
COVERAGE_INFO := $(REPORTS_DIR)/coverage.info
COVERAGE_JSON := $(REPORTS_DIR)/coverage.json
COVERAGE_PER_REQ := $(REPORTS_DIR)/coverage_per_req.json
JUDGE_JSON := $(REPORTS_DIR)/judge.json
JUNIT_XML := $(REPORTS_DIR)/junit.xml
SYNTH_REPORT := $(REPORTS_DIR)/synth_report.json
FORMAL_DIR := $(REPORTS_DIR)/formal
MUTATION_DIR := $(REPORTS_DIR)/mutation

VERILATOR_INCLUDES := -Itb -Iverification
VERILATOR_LINT_FLAGS := -sv --timing -Wall -Wno-UNUSEDSIGNAL $(VERILATOR_INCLUDES)
VERILATOR_BUILD_FLAGS := -sv --timing -O3 -Wall -Wno-fatal -Wno-UNUSEDSIGNAL $(VERILATOR_INCLUDES)
COV_FLAGS ?= --coverage

.PHONY: help quick all env spec lint sim_run coverage_collect coverage_json judge junit check report synth formal_core formal_soft smoke mutate dashboards mutant_report freeze clean distclean

help: ## Show common targets
	@awk -F':.*##' '/^[a-zA-Z0-9_-]+:.*##/ {printf "\033[36m%-18s\033[0m %s\n", $$1, $$2}' $(MAKEFILE_LIST) | sort

quick: env spec lint dashboards ## Spec→Tests/SVAs, lint, sim+coverage+judge + dashboards

all: env spec lint report synth formal_core mutate dashboards ## Full verification + QoR flow

env: ## Capture tool versions and host details
	$(PYTHON) scripts/env_report.py --out $(ENV_JSON)

spec: ## Lint spec and regenerate requirements, plan, and SVAs
	$(PYTHON) scripts/spec_lint.py --spec docs/spec.md
	$(PYTHON) scripts/spec2tests.py --spec docs/spec.md --out verification
	$(PYTHON) scripts/spec2sva.py --spec docs/spec.md --out tb/top_asserts.sv

lint: ## Run Verible and Verilator lint
	$(VERIBLE_FORMAT) --inplace $(RTL_FILES) $(TB_FILES) $(VERIF_SV) || true
	$(VERILATOR) --lint-only $(VERILATOR_LINT_FLAGS) $(SV_SOURCES)
	$(VERIBLE_LINT) $(VERIBLE_RULES_ARG) $(RTL_FILES) $(TB_FILES)

$(BUILD_DIR):
	mkdir -p $@

$(SIM_BIN): $(SV_SOURCES) verification/svas.sv sim/main.cpp | $(BUILD_DIR)
	$(VERILATOR) $(VERILATOR_BUILD_FLAGS) $(COV_FLAGS) --cc --exe --build --top-module $(TOP_TB) $(SV_SOURCES) sim/main.cpp -Mdir $(BUILD_DIR)/obj_dir

$(REPORTS_DIR):
	mkdir -p $@

sim_run: $(SIM_BIN) | $(REPORTS_DIR) ## Run compiled simulation and convert to JSON
	@echo "== Run simulation (seed $(SEED)) =="
	@$(PYTHON) scripts/run_sim.py \
		--sim-bin $(SIM_BIN) \
		--sim-args "$(SIM_ARGS)" \
		--log $(SIM_LOG) \
		--reports $(REPORTS_DIR) \
		--seed $(SEED) \
		--manifest $(RUN_MANIFEST) \
		--flaky-retries $(FLAKE_RETRIES)
	@if [ -f $(BUILD_DIR)/obj_dir/coverage.dat ]; then cp $(BUILD_DIR)/obj_dir/coverage.dat $(REPORTS_DIR)/coverage.dat; fi

coverage_collect: | $(REPORTS_DIR) ## Generate lcov coverage report
	@if [ -f $(REPORTS_DIR)/coverage.dat ]; then \
		mkdir -p $(REPORTS_DIR)/cov_annotate; \
		verilator_coverage --annotate $(REPORTS_DIR)/cov_annotate --write-info $(COVERAGE_INFO) $(REPORTS_DIR)/coverage.dat >/dev/null 2>&1 || true; \
		echo "Coverage summary -> $(COVERAGE_INFO)"; \
	else \
		echo "No coverage data found"; \
	fi

coverage_json: coverage_collect ## Convert coverage data to JSON
	@if [ -f $(COVERAGE_INFO) ]; then \
		$(PYTHON) scripts/coverage_to_json.py --in $(COVERAGE_INFO) --out $(COVERAGE_JSON); \
	else \
		echo "Skipping coverage_to_json (coverage.info missing)"; \
	fi
	$(PYTHON) scripts/coverage_per_req.py --reqs verification/reqs.yml --sim $(SIM_REPORT) --cov $(COVERAGE_JSON) --log $(SIM_LOG) --tb tb/top_tb.sv --out $(COVERAGE_PER_REQ)

judge: ## Triage simulation outcomes
	$(PYTHON) scripts/judge.py --reports $(REPORTS_DIR) --out $(JUDGE_JSON)

junit: ## Emit JUnit XML for CI
	$(PYTHON) scripts/sim_to_junit.py --in $(SIM_REPORT) --out $(JUNIT_XML)

check: ## Enforce coverage and policy gates
	$(PYTHON) scripts/check_gates.py --policies policies.yml --reports $(REPORTS_DIR) --reqs verification/reqs.yml --coverage $(COVERAGE_JSON) --per-req $(COVERAGE_PER_REQ)

report: spec $(SIM_BIN) ## Simulation + coverage + judge
	$(MAKE) sim_run
	$(MAKE) coverage_json
	$(PYTHON) scripts/judge.py --reports $(REPORTS_DIR) --out $(JUDGE_JSON)
	$(PYTHON) scripts/sim_to_junit.py --in $(SIM_REPORT) --out $(JUNIT_XML)
	$(PYTHON) scripts/check_gates.py --policies policies.yml --reports $(REPORTS_DIR) --reqs verification/reqs.yml --coverage $(COVERAGE_JSON) --per-req $(COVERAGE_PER_REQ)

synth: ## Run UHDM-Yosys synthesis and enforce latch policy
	@mkdir -p $(REPORTS_DIR)
	@yosys_version="$$($(YOSYS_SV) -V | head -n1)"; \
	if $(YOSYS_SV) -Q -p "help read_systemverilog" >/dev/null 2>&1; then \
		echo "[synth] Using UHDM-enabled $(YOSYS_SV)"; \
		$(YOSYS_SV) -p "plugin -i systemverilog" -s synth/synth.ys -l synth/yosys.log; \
		echo '{"uhdm_used": true}' > $(REPORTS_DIR)/synth_caps.json; \
		uhdm_flag=true; \
	else \
		echo "[synth] UHDM not available — using fallback read_verilog -sv"; \
		$(YOSYS_SV) -Q -p "read_verilog -sv rtl/top.sv; hierarchy -top top; proc; opt; check; write_json synth/out.json" | tee synth/yosys.log; \
		echo '{"uhdm_used": false}' > $(REPORTS_DIR)/synth_caps.json; \
		uhdm_flag=false; \
	fi; \
	$(PYTHON) scripts/update_manifest.py --manifest $(RUN_MANIFEST) --yosys "$$yosys_version" --uhdm $$uhdm_flag; \
	$(PYTHON) scripts/yosys_to_json.py --log synth/yosys.log --out $(SYNTH_REPORT) --policies policies.yml; \
	$(PYTHON) scripts/check_gates.py --policies policies.yml --reports $(REPORTS_DIR) --stage synth

formal_core: ## Execute core SymbiYosys profiles
	$(PYTHON) scripts/run_formal.py --profiles formal/profiles/core.yml --out $(FORMAL_DIR) --sby $(SBY)

formal_soft: ## Run formal but continue on failure (useful for ad-hoc testing)
	@$(MAKE) --no-print-directory formal_core || echo "[formal] Soft mode: ignoring formal failure"

mutant_report: ## Internal: run report with mutant overrides
	@$(MAKE) REPORTS_DIR=$(MUTANT_OUT) report

mutate: ## Generate mutants and evaluate kill rate
	$(PYTHON) scripts/mutate.py --rtl rtl --out mutants
	$(PYTHON) scripts/run_mutants.py --mutants mutants --reports $(MUTATION_DIR) --make $(MAKE) --seed $(SEED) --cwd $(CURDIR)

dashboards: report ## Build dashboards and static site
	$(PYTHON) scripts/report_dashboard.py --reports $(REPORTS_DIR) --reqs verification/reqs.yml --out $(REPORTS_DIR)
	@if [ -f $(REPORTS_DIR)/coverage_badge.svg ]; then cp -f $(REPORTS_DIR)/coverage_badge.svg docs/coverage_badge.svg; fi

freeze: ## Run smoke + synth and tag a template release
	REPORTS_DIR=reports/_smoke SEED=1 $(MAKE) -e quick
	$(MAKE) synth
	git tag -f template-v1


smoke: ## Quick local run with canned seed and smoke reports
	REPORTS_DIR=reports/_smoke SEED=42 $(MAKE) -e quick

clean: ## Remove generated reports and builds
	rm -rf $(BUILD_DIR) reports reports/run_manifest.json synth/out.json synth/yosys.log mutants

distclean: clean ## Remove formal artefacts and cached data
	rm -rf formal/*/PASS formal/*/engine_* formal/*/status* formal/*/model $(FORMAL_DIR)
