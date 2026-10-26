# ==============================================================================
# External Makefile for BMMGrid Lean 4 Formalization
# ==============================================================================
# Toolchain : leanprover/lean4:v4.27.0 (see lean-toolchain)
# Mathlib 4 : a3a10db0e9d66acbebf76c5e6a135066525ac900 (v4.27.0, see lakefile.toml)
#
# Quick start (external environment with elan / lake installed):
#   make setup   # Fetch Mathlib 4 precompiled .olean cache via `lake exe cache get`
#   make         # Build all 13 BMMGrid modules + root gate BMMGrid.lean + FORMALIZATION.pdf
#   make doc     # Compile FORMALIZATION.tex -> FORMALIZATION.pdf via pdflatex
#   make audit   # Run static escape-hatch, line-count, and FORMALIZATION.tex parity checks
#   make verify  # Run `make audit`, `make build`, and `make doc`
# ==============================================================================

SHELL       := /bin/bash
export PATH := $(HOME)/.elan/bin:$(PATH)
LAKE        ?= lake
PDFLATEX    ?= pdflatex
PAPER_MD5   := 0f1591869b4096ffd6d44b984ef79960

LEAN_FILES := \
	BMMGrid.lean \
	BMMGrid/Defs.lean \
	BMMGrid/CostMonadAndLinter.lean \
	BMMGrid/ArithRAM.lean \
	BMMGrid/CitedResults.lean \
	BMMGrid/KLMUniformity.lean \
	BMMGrid/ObliviousSampler.lean \
	BMMGrid/ApproxGridNorm.lean \
	BMMGrid/MinDegreeAndDyadicSift.lean \
	BMMGrid/Decomp2D.lean \
	BMMGrid/DyadicBucketingAndGoodCube.lean \
	BMMGrid/Decomp3DPotential.lean \
	BMMGrid/Decomp3D.lean \
	BMMGrid/TriangleAndBMM.lean

.PHONY: all build doc setup cache verify audit check clean help \
        defs cost arithram cited klm sampler approx sift decomp2d \
        goodcube potential3d decomp3d bmm root

all: build doc

## Fetch precompiled Mathlib 4 .olean cache (avoids building Mathlib from source)
setup cache:
	$(LAKE) exe cache get

## Build all BMMGrid modules and run compile-time auditors in BMMGrid.lean
build:
	@if [ ! -d ".lake/packages/mathlib" ]; then \
		echo "Fetching Mathlib 4 cache first (run 'make setup' explicitly to refresh)..."; \
		$(LAKE) exe cache get; \
	fi
	$(LAKE) build BMMGrid

## Compile FORMALIZATION.tex -> FORMALIZATION.pdf
doc: FORMALIZATION.pdf

FORMALIZATION.pdf: FORMALIZATION.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error FORMALIZATION.tex >/dev/null
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error FORMALIZATION.tex >/dev/null
	! grep -En 'Overfull \\[hv]box|Package hyperref Warning|LaTeX Warning:.*(Rerun|undefined)' FORMALIZATION.log
	rm -f FORMALIZATION.aux FORMALIZATION.log FORMALIZATION.out

## Individual module targets (topological dependency order)
defs:
	$(LAKE) build BMMGrid.Defs

cost:
	$(LAKE) build BMMGrid.CostMonadAndLinter

arithram:
	$(LAKE) build BMMGrid.ArithRAM

cited:
	$(LAKE) build BMMGrid.CitedResults

klm:
	$(LAKE) build BMMGrid.KLMUniformity

sampler:
	$(LAKE) build BMMGrid.ObliviousSampler

approx:
	$(LAKE) build BMMGrid.ApproxGridNorm

sift:
	$(LAKE) build BMMGrid.MinDegreeAndDyadicSift

decomp2d:
	$(LAKE) build BMMGrid.Decomp2D

goodcube:
	$(LAKE) build BMMGrid.DyadicBucketingAndGoodCube

potential3d:
	$(LAKE) build BMMGrid.Decomp3DPotential

decomp3d:
	$(LAKE) build BMMGrid.Decomp3D

bmm:
	$(LAKE) build BMMGrid.TriangleAndBMM

root:
	$(LAKE) build BMMGrid

## Static hygiene, escape-hatch, and FORMALIZATION.tex call-site parity checks
audit check:
	@echo "[1/5] Checking for forbidden escape hatches across $(words $(LEAN_FILES)) Lean files..."
	@! grep -En '^[[:space:]]*(axiom|unsafe|opaque|partial)[[:space:]]' $(LEAN_FILES)
	@! (grep -En '\b(sorry|admit|native_decide|implemented_by|extern)\b' $(LEAN_FILES) | grep -v 'CostMonadAndLinter\.lean:.*implemented_by.*extern')
	@echo "[2/5] Checking file line-count invariants (< 60 LoC for BMMGrid.lean, < 5,000 LoC per module)..."
	@test $$(wc -l < BMMGrid.lean) -lt 60
	@for f in $(LEAN_FILES); do \
		lines=$$(wc -l < "$$f"); \
		if [ "$$lines" -ge 5000 ]; then \
			echo "ERROR: $$f has $$lines lines (>= 5000)"; exit 1; \
		fi; \
	done
	@echo "[3/5] Checking 107-site CostM payload table parity between BMMGrid/*.lean and FORMALIZATION.tex..."
	@python3 scripts/gen_payload_table.py --check
	@echo "[4/5] Checking paper.tex MD5 pin ($(PAPER_MD5))..."
	@grep -Fq "$(PAPER_MD5)" FORMALIZATION.tex || { echo "ERROR: FORMALIZATION.tex missing PAPER_MD5 $(PAPER_MD5)"; exit 1; }
	@if [ -f ../paper.tex ]; then \
		actual_md5=$$(md5sum ../paper.tex | awk '{print $$1}'); \
		test "$$actual_md5" = "$(PAPER_MD5)" || { echo "ERROR: ../paper.tex MD5 $$actual_md5 != $(PAPER_MD5)"; exit 1; }; \
	fi
	@echo "[5/5] Checking cited paper LaTeX labels in Lean docstrings and FORMALIZATION.tex against ../paper.tex..."
	@if [ -f ../paper.tex ]; then \
		for lbl in $$(python3 -c 'import pathlib, re; files = [pathlib.Path("FORMALIZATION.tex")] + sorted(pathlib.Path(".").rglob("*.lean")); txt = "\n".join(f.read_text() for f in files); raw = re.findall(r"(?:\\eqref|\\label|\\Cref|textbackslash\s*label)\s*\\?\{((?:eq|lem|thm|prop|rem|app|line|tab|cor|def|alg|clm):[^}\\]+)\\?\}", txt); print("\n".join(sorted(set(raw))))'); do \
			grep -Fq "\\label{$$lbl}" ../paper.tex || { echo "ERROR: phantom paper label $$lbl not in ../paper.tex"; exit 1; }; \
		done; \
	fi
	@echo "All static audit checks passed (0 escape hatches, 107/107 payload sites, 106 on-path, PAPER_MD5=$(PAPER_MD5))."

## Run static audit + full Lean 4 build + FORMALIZATION.pdf compilation
verify: audit build doc

## Clean Lake build artifacts and FORMALIZATION.pdf
clean:
	rm -f FORMALIZATION.pdf FORMALIZATION.aux FORMALIZATION.log FORMALIZATION.out
	$(LAKE) clean

help:
	@echo "BMMGrid Lean 4 Formalization Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make setup     Fetch precompiled Mathlib 4 .olean cache (lake exe cache get)"
	@echo "  make [all]     Build all 13 BMMGrid modules, root gate BMMGrid.lean, and FORMALIZATION.pdf"
	@echo "  make build     Build all 13 BMMGrid modules and root gate BMMGrid.lean"
	@echo "  make doc       Compile FORMALIZATION.tex -> FORMALIZATION.pdf via pdflatex"
	@echo "  make audit     Run static escape-hatch, line-count, and FORMALIZATION.tex parity checks"
	@echo "  make verify    Run 'make audit', 'make build', and 'make doc'"
	@echo "  make <module>  Build a single module (defs, cost, arithram, cited, klm,"
	@echo "                 sampler, approx, sift, decomp2d, goodcube, potential3d,"
	@echo "                 decomp3d, bmm, root)"
	@echo "  make clean     Clean Lake build outputs and FORMALIZATION.pdf"
