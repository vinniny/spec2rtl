VERIBLE_BIN := $(PWD)/tools/verible/bin
PATH := $(VERIBLE_BIN):$(PATH)
VERIBLE_FORMAT := $(VERIBLE_BIN)/verible-verilog-format
VERIBLE_LINT := $(VERIBLE_BIN)/verible-verilog-lint
PRE_COMMIT ?= pre-commit

SEED ?= 1234
LINE_COV_MIN ?= 0.80
TOGGLE_COV_MIN ?= 0.70

SCRIPTS_DIR := scripts
SPEC := docs/spec.md
DEV_LOOP := $(SCRIPTS_DIR)/dev_loop.sh
REPORTS := reports
SIM_LOG := $(REPORTS)/sim.log

YOSYS_SV ?= ./tools/yosys-sv
VERILATOR ?= verilator
VERILATOR_TIMING ?= --timing
VERILATOR_INCLUDES ?= -Itb -Iverification
VERILATOR_LINT_FLAGS ?= -sv $(VERILATOR_TIMING) -Wall -Wno-UNUSEDSIGNAL $(VERILATOR_INCLUDES)
VERILATOR_BUILD_FLAGS ?= -sv $(VERILATOR_TIMING) -O3 -Wall -Wno-fatal -Wno-UNUSEDSIGNAL $(VERILATOR_INCLUDES)
COV_FLAGS ?= --coverage
TOP_TB ?= top_tb
SIM_ARGS := +seed=$(SEED)
SIM_BIN := build/sim/obj_dir/V$(TOP_TB)

RTL ?= $(wildcard rtl/*.sv)
TB_ALL := $(wildcard tb/*.sv)
TB := $(filter-out tb/top_asserts.sv,$(TB_ALL))
VERIF_SV := $(wildcard verification/*.sv)
SV_SOURCES = $(RTL) $(TB)
SIM_SOURCES = $(SV_SOURCES)
SV_FORMAT_SOURCES = $(RTL) $(TB_ALL) $(VERIF_SV)

.PHONY: all check format lint lint-verilator lint-verible sim run test judge report cov cov_summarize trace trace_md synth formal formal_all dashboards badge mutate env junit clean hooks flaky_check patch \
	pre-commit spec2rtl spec2sva spec2tests generate dev
all: lint check synth formal_all dashboards badge

format:
	@echo "== Verible format =="
	$(VERIBLE_FORMAT) --inplace $(SV_FORMAT_SOURCES)

lint: lint-verilator lint-verible

lint-verilator:
	@echo "== Verilator lint =="
	$(VERILATOR) --lint-only $(VERILATOR_LINT_FLAGS) $(SV_SOURCES)

lint-verible:
	@echo "== Verible lint =="
	$(VERIBLE_LINT) $(SV_FORMAT_SOURCES)

sim: $(SIM_BIN)

run: test

$(SIM_BIN): $(SIM_SOURCES) verification/svas.sv sim/main.cpp | build/sim
	$(VERILATOR) $(VERILATOR_BUILD_FLAGS) $(COV_FLAGS) --cc --exe --build \
	  --top-module $(TOP_TB) $(SIM_SOURCES) sim/main.cpp -Mdir build/sim/obj_dir

synth: synth/out.json
	@true

synth/out.json: $(RTL) synth/synth.ys | synth_dir
	@echo "== Yosys UHDM synth =="
	$(YOSYS_SV) -s synth/synth.ys | tee synth/yosys.log
	@python3 $(SCRIPTS_DIR)/yosys_to_json.py
	@python3 -c "import json, sys; from pathlib import Path; data=json.loads(Path('reports/synth_report.json').read_text()); sys.exit(0 if not data.get('has_latch') else 1)" || (echo 'Latch detected in synthesis'; exit 1)

build/sim:
	mkdir -p $@

synth_dir:
	mkdir -p synth

$(REPORTS):
	mkdir -p $@

hooks:
	$(PRE_COMMIT) install

pre-commit:
	$(PRE_COMMIT) run --all-files

spec2rtl: $(SPEC)
	python3 $(SCRIPTS_DIR)/spec2rtl.py --spec $(SPEC)

spec2sva: $(SPEC)
	python3 $(SCRIPTS_DIR)/spec2sva.py --spec $(SPEC)

spec2tests:
	python3 $(SCRIPTS_DIR)/spec2tests.py

generate: spec2rtl spec2sva spec2tests

dev:
	$(DEV_LOOP)

test: sim | $(REPORTS)
	@echo "== Run sim =="
	@bash -lc 'start=$$(python3 -c "import time; print(time.time())"); \
	  set -o pipefail; \
	  $(SIM_BIN) $(SIM_ARGS) 2>&1 | tee $(SIM_LOG); \
	  status=$${PIPESTATUS[0]}; \
	  end=$$(python3 -c "import time; print(time.time())"); \
	  duration=$$(python3 -c "print(float('$$end')-float('$$start'))"); \
	  python3 $(SCRIPTS_DIR)/sim_to_json.py $(SIM_LOG) $$duration; \
	  exit $$status'

judge:
	@-$(MAKE) test
	@python3 $(SCRIPTS_DIR)/judge.py

cov:
	@if [ -f $(REPORTS)/coverage.dat ]; then \
	  mkdir -p $(REPORTS)/cov_annotate; \
	  verilator_coverage --annotate $(REPORTS)/cov_annotate --write-info $(REPORTS)/coverage.info $(REPORTS)/coverage.dat >/dev/null 2>&1 || true; \
	  echo "Coverage summary -> $(REPORTS)/coverage.info"; \
	else \
	  echo "No coverage data found"; \
	fi

cov_summarize:
	@if [ ! -f $(REPORTS)/coverage.info ]; then $(MAKE) cov; fi
	@python3 $(SCRIPTS_DIR)/coverage_to_json.py
	@python3 $(SCRIPTS_DIR)/coverage_per_req.py

report: | $(REPORTS)
	@-$(MAKE) judge
	@$(MAKE) cov_summarize
	@status=$$(jq -r '.status' $(REPORTS)/sim_report.json); \
	 echo "=== SIM REPORT ==="; cat $(REPORTS)/sim_report.json; \
	 echo "=== JUDGE ==="; cat $(REPORTS)/judge.json; \
	 if [ "$$status" != "pass" ]; then \
	   python3 $(SCRIPTS_DIR)/wave_slice.py || true; \
	   echo "Simulation failed"; \
	   exit 1; \
	 fi
trace: cov_summarize
	@python3 $(SCRIPTS_DIR)/trace_matrix.py

trace_md: trace
	@python3 $(SCRIPTS_DIR)/trace_to_md.py

check: report cov_summarize
	@LINE_COV_MIN=$(LINE_COV_MIN) TOGGLE_COV_MIN=$(TOGGLE_COV_MIN) python3 $(SCRIPTS_DIR)/check_gates.py

clean:
	rm -rf build synth/out.json $(REPORTS)

flaky_check:
	@if [ -f reports/sim_report.json ] && [ "$$(jq -r '.status' reports/sim_report.json)" != "pass" ]; then \
	  sig1=$$(jq -r .signature reports/sim_report.json); \
	  $(MAKE) report; \
	  sig2=$$(jq -r .signature reports/sim_report.json); \
	  if [ "$$sig1" != "$$sig2" ]; then echo "FLAKY (same SEED)"; exit 1; fi; \
	fi

formal: | $(REPORTS)
	@sby -f formal/top.sby | tee reports/formal.log
	@grep -q "DONE (PASS" reports/formal.log || (echo "Formal failed"; exit 1)

formal_all: formal
	@[ -f formal/top_protocol.sby ] && sby -f formal/top_protocol.sby | tee -a reports/formal.log || true

dashboards: | $(REPORTS)
	@python3 $(SCRIPTS_DIR)/report_dashboard.py

badge: | $(REPORTS)
	@python3 $(SCRIPTS_DIR)/coverage_badge.py

mutate: | $(REPORTS)
	@python3 $(SCRIPTS_DIR)/mutate.py
	@$(MAKE) -e RTL="rtl/top_mut.sv" report || true
	@test $$(jq -r '.status' $(REPORTS)/sim_report.json) = "fail" \
	  || (echo "Mutation survived (tests too weak)"; rm -f rtl/top_mut.sv; exit 1)
	@rm -f rtl/top_mut.sv
	@$(MAKE) report

env:
	@python3 $(SCRIPTS_DIR)/env_report.py | tee reports/env.json

junit: report
	@python3 $(SCRIPTS_DIR)/sim_to_junit.py

patch: judge
	@python3 $(SCRIPTS_DIR)/draft_patch.py
