# GridSentinel -- developer entry points.
#
# THE ONE THING TO KNOW (macOS):
#     the interpreter MUST be invoked as `arch -arm64 .venv/bin/python`,
#     and NEVER wrapped in `timeout`.
# .venv/bin/python is a universal binary.  Anything that starts it from an
# x86_64 parent -- and this machine's /usr/bin/timeout and coreutils gtimeout
# are x86_64 -- makes it select its x86_64 slice, whereupon z3's arm64
# libz3.dylib refuses to load and pandapower runs under translation at a
# fraction of the speed.  Several people have lost an afternoon to this.
# Every recipe below goes through $(PY), which encodes the workaround.
#
# On Linux (CI) `arch -arm64` does not exist and is not needed, so ARCH is
# empty there.  The workaround is macOS-local, not a portable requirement.

VENV      ?= .venv
SEED      ?= 0
N_PER_FAMILY ?= 8
HORIZON   ?= 6000

UNAME_S := $(shell uname -s)
UNAME_M := $(shell uname -m)
ifeq ($(UNAME_S),Darwin)
ifeq ($(UNAME_M),arm64)
ARCH := arch -arm64
endif
endif

PY  := $(ARCH) $(VENV)/bin/python
PIP := $(PY) -m pip

.DEFAULT_GOAL := help
.PHONY: help install test verify experiment attacks figures lint all clean distclean

help:  ## show this help
	@echo "GridSentinel -- make targets"
	@echo ""
	@echo "  make install     create/refresh $(VENV) and install the package (editable) + dev extras"
	@echo "  make test        pytest, tests/            (~2.5 min)"
	@echo "  make verify      Z3 proof suite            (~1 min; fails on a proof regression)"
	@echo "  make experiment  run.py    -- v1 shield experiment, SEED=$(SEED)"
	@echo "  make attacks     run_v2.py -- adversary catalogue + drive plant, SEED=$(SEED)"
	@echo "  make figures     re-render figures from out/results*.json (no re-run)"
	@echo "  make lint        ruff if installed, else pyflakes, else a syntax check"
	@echo "  make all         install test verify experiment attacks"
	@echo "  make clean       caches and build artefacts   (keeps out/ and models/)"
	@echo "  make distclean   clean + out/ + trained models"
	@echo ""
	@echo "Interpreter: $(PY)"
	@echo "  On macOS the 'arch -arm64' prefix is mandatory and 'timeout' must"
	@echo "  never wrap it -- see the comment at the top of this Makefile."
	@echo ""
	@echo "Read docs/PROOF.md 8.7 and docs/THREATMODEL.md before quoting any"
	@echo "safety result: the headline claim is falsified under a local"
	@echo "merging-unit key compromise."

install:  ## create the venv if absent and install the package + dev extras
	@test -d $(VENV) || python3 -m venv $(VENV)
	$(PIP) install --upgrade pip
	$(PIP) install -e ".[dev]"

test:  ## property + unit tests (75 tests, ~2.5 min)
	$(PY) -m pytest tests/

verify:  ## Z3 proof suite; non-zero exit if any layer regresses
	$(PY) -m gs verify

experiment:  ## run.py: three arms over the scenario catalogue -> out/results.json
	$(PY) run.py --seed $(SEED) --n-per-family $(N_PER_FAMILY)

attacks:  ## run_v2.py: adversary catalogue + VFD/rotor plant -> out/results_v2.json
	$(PY) run_v2.py --seed $(SEED) --horizon $(HORIZON)

figures:  ## re-render figures from the JSON already in out/
	@test -f out/results.json || { echo "out/results.json missing -- run 'make experiment' first"; exit 1; }
	$(PY) -m gs.report out/results.json
	@test -f out/results_v2.json && $(PY) -m gs.report_v2 out/results_v2.json \
		|| echo "out/results_v2.json missing -- skipping v2 figures (run 'make attacks')"

lint:  ## ruff if available, else pyflakes, else compile-only syntax check
	@if $(PY) -c "import ruff" 2>/dev/null || command -v $(VENV)/bin/ruff >/dev/null 2>&1; then \
		$(ARCH) $(VENV)/bin/ruff check gs run.py run_v2.py tests ; \
	elif $(PY) -c "import pyflakes" 2>/dev/null; then \
		echo "ruff not installed; falling back to pyflakes"; \
		$(PY) -m pyflakes gs run.py run_v2.py tests ; \
	else \
		echo "neither ruff nor pyflakes installed ('make install' provides ruff);"; \
		echo "falling back to a syntax-only check"; \
		$(PY) -m compileall -q gs run.py run_v2.py tests ; \
	fi

all: install test verify experiment attacks  ## everything, in order

clean:  ## caches and build artefacts; leaves out/ and models/ alone
	rm -rf .pytest_cache .hypothesis build dist *.egg-info
	find . -path ./$(VENV) -prune -o -name '__pycache__' -type d -print0 \
		| xargs -0 rm -rf 2>/dev/null || true
	find . -path ./$(VENV) -prune -o -name '*.pyc' -print0 \
		| xargs -0 rm -f 2>/dev/null || true

distclean: clean  ## also deletes results, figures and the trained policy
	rm -rf out models/*.joblib
