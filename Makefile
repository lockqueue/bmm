# ==============================================================================
# Top-Level External Makefile — Combinatorial BMM Grid Regularity (Lean 4)
# ==============================================================================
# Lean 4   : lean/ (leanprover/lean4:v4.27.0, Mathlib 4 a3a10db0e9d66acbebf76c5e6a135066525ac900)
#
# Quick start:
#   make setup   # Fetch precompiled Mathlib 4 .olean cache in lean/
#   make lean    # Typecheck all 13 BMMGrid modules + root gate BMMGrid.lean
#   make doc     # Compile lean/FORMALIZATION.tex -> lean/FORMALIZATION.pdf
#   make paper   # Compile paper.tex -> paper.pdf
#   make audit   # Run static Lean + FORMALIZATION.tex parity checks
#   make verify  # Run audit + lean + doc
#   make dist    # Create standalone external zip archive bmm_grid_regularity_external.zip
# ==============================================================================

SHELL       := /bin/bash
export PATH := $(HOME)/.elan/bin:$(PATH)
PDFLATEX    ?= pdflatex
DIST_ZIP    := bmm_grid_regularity_external.zip

.PHONY: all lean build doc paper setup cache audit check verify dist clean help

all: lean doc

## Fetch precompiled Mathlib 4 .olean cache
setup cache:
	$(MAKE) -C lean setup

## Build and verify the Lean 4 formalization in lean/
lean build:
	$(MAKE) -C lean build

## Compile lean/FORMALIZATION.tex -> lean/FORMALIZATION.pdf
doc:
	$(MAKE) -C lean doc

## Compile paper.tex -> paper.pdf
paper: paper.pdf

paper.pdf: paper.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >/dev/null
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >/dev/null
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error paper.tex >/dev/null
	! grep -En 'Overfull \\[hv]box|Package hyperref Warning|LaTeX Warning:.*(Rerun|undefined)' paper.log
	rm -f paper.aux paper.log paper.out paper.toc

## Run static Lean & FORMALIZATION.tex call-site parity checks
audit check:
	$(MAKE) -C lean audit

## Full verification: run static audit, typecheck Lean 4 proof, and build FORMALIZATION.pdf
verify: audit lean doc

## Package a standalone external zip archive
dist: audit doc paper.pdf
	rm -f $(DIST_ZIP)
	zip -q $(DIST_ZIP) \
		README.md \
		LICENSE \
		Makefile \
		paper.tex \
		paper.pdf \
		lean/Makefile \
		lean/LICENSE \
		lean/lean-toolchain \
		lean/lakefile.toml \
		lean/lake-manifest.json \
		lean/BMMGrid.lean \
		lean/BMMGrid/*.lean \
		lean/scripts/gen_payload_table.py \
		lean/FORMALIZATION.tex \
		lean/FORMALIZATION.pdf \
		lean/SOURCES.md
	@echo "Created standalone external zip archive: $(DIST_ZIP)"

## Clean Lean build outputs, FORMALIZATION.pdf, paper.pdf, and archive
clean:
	rm -f $(DIST_ZIP) paper.pdf paper.aux paper.log paper.out paper.toc
	$(MAKE) -C lean clean

help:
	@echo "Combinatorial BMM Grid Regularity — Top-Level External Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  make [all]    Build all 13 BMMGrid modules, root gate BMMGrid.lean, and lean/FORMALIZATION.pdf"
	@echo "  make lean     Build all 13 BMMGrid modules and root gate BMMGrid.lean"
	@echo "  make doc      Compile lean/FORMALIZATION.tex -> lean/FORMALIZATION.pdf"
	@echo "  make paper    Compile paper.tex -> paper.pdf"
	@echo "  make setup    Fetch precompiled Mathlib 4 .olean cache (lake exe cache get)"
	@echo "  make audit    Run static escape-hatch, line-count, and FORMALIZATION.tex parity checks"
	@echo "  make verify   Run 'make audit', 'make lean', and 'make doc'"
	@echo "  make dist     Create standalone zip archive $(DIST_ZIP)"
	@echo "  make clean    Remove Lake build artifacts, lean/FORMALIZATION.pdf, paper.pdf, and $(DIST_ZIP)"
