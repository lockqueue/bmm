# Combinatorial Boolean Matrix Multiplication in $n^3 / 2^{\Omega(\sqrt{\log n})}$ Time

## Authors

-   **Piaoyang Cui** (Google DeepMind)
-   **Yiming Liu** (Google DeepMind)
-   **David Woodruff** (Google Research and Carnegie Mellon University)

*Authors are listed in alphabetical order.*

## Abstract

For over fifty years, combinatorial algorithms for Boolean matrix multiplication
(BMM) and triangle detection saved only polylogarithmic factors over cubic time.
Abboud, Fischer, Kelley, Lovett, and Meka (STOC 2024) broke this barrier with a
deterministic $n^3 / 2^{\Omega((\log n)^{1/7})}$-time algorithm, based on a
regularity decomposition for the grid norms of Kelley, Lovett, and Meka. They
asked whether time $n^3 / 2^{\Omega(\sqrt{\log n})}$ is achievable, observing
that Behrend-type constructions might obstruct improvements beyond this scale
within grid regularity.

We show that it is: we give a deterministic combinatorial algorithm for BMM and
triangle detection running in $O(n^3 / 2^{\Omega(\sqrt{\log n})})$ time. It uses
only comparisons and arithmetic on $O(\log n)$-bit words, and the bound holds
unchanged on a pointer machine.

Our main technical result decomposes any pair of Boolean matrices into
$\exp(O(d^2 / \varepsilon^2))$ pieces, each sparse or $(\varepsilon, 2,
2d)$-grid-regular, for grid-norm parameter $d$ and regularity $\varepsilon$;
this improves the $\exp(d^7 \mathrm{poly}(1/\varepsilon))$ bound of Abboud
et al. Four ideas drive the improvement: sifting at dyadic density scales,
paying vertex loss only when the density jumps; a cheaper deterministic
grid-norm estimator via an exact outer average and two-stage oblivious sampling;
a fractional density-weighted potential in place of unweighted volume; and a
recursion that converts density jumps directly into depth. We show that a single
step of our sifting procedure can be forced to retain only an
$\exp(-\Omega(d^2))$ fraction of the rows, giving evidence that the exponent
$1/2$ is the limit of this approach.

Formal versions of the decomposition, BMM, and triangle-detection theorems are
machine-checked in Lean 4, conditional on explicit hypotheses that transcribe
the cited sampler and extractor constructions. The formal running-time bounds
are declared-charge cost bounds rather than machine-model step counts; Section 8
of the paper and `lean/FORMALIZATION.pdf` give the exact scope.

## License

The Lean 4 formalization in `lean/` (the `BMMGrid` sources,
`lean/scripts/gen_payload_table.py`, `lean/lakefile.toml`, the Makefiles, and
the Formalization Notes `lean/FORMALIZATION.tex` / `.pdf`) is licensed under the
Apache License, Version 2.0; see `LICENSE` (identical copy in `lean/LICENSE`).

The paper (`paper.tex`, `paper.pdf`) is not covered by that license. The Lean 4
toolchain and Mathlib fetched by `make setup` are distributed under their own
Apache-2.0 licenses.

## Directory Structure

```text
.
├── README.md                  # Overview, authors, abstract, and build instructions
├── LICENSE                    # Apache License 2.0 (covers lean/ and the Makefiles; not the paper)
├── Makefile                   # Top-level Makefile (Lean 4 build, docs, and verification)
├── paper.tex                  # LaTeX source of the paper
├── paper.pdf                  # Compiled PDF of the paper
└── lean/                      # Machine-checked Lean 4 formalization (BMMGrid)
    ├── LICENSE                # Apache License 2.0 (copy)
    ├── Makefile               # Standalone Lake Makefile for building and auditing BMMGrid
    ├── lean-toolchain         # Lean 4 toolchain pin (leanprover/lean4:v4.27.0)
    ├── lakefile.toml          # Lake package configuration
    ├── lake-manifest.json     # Locked Mathlib 4 dependency manifest
    ├── FORMALIZATION.tex      # LaTeX source of the Formalization Notes (Classes A-D)
    ├── FORMALIZATION.pdf      # Compiled PDF of the Formalization Notes (Classes A-D)
    ├── SOURCES.md             # Primary-source locators, SHA-256 digests, and verbatim quotes
    ├── scripts/               # Self-contained audit and table-generation scripts
    │   └── gen_payload_table.py
    ├── BMMGrid.lean           # Root trust-boundary module (< 60 LoC) and compile-time gates
    └── BMMGrid/               # 13 Lean 4 implementation and proof modules
        ├── Defs.lean
        ├── CostMonadAndLinter.lean
        ├── ArithRAM.lean
        ├── CitedResults.lean
        ├── KLMUniformity.lean
        ├── ObliviousSampler.lean
        ├── ApproxGridNorm.lean
        ├── MinDegreeAndDyadicSift.lean
        ├── Decomp2D.lean
        ├── DyadicBucketingAndGoodCube.lean
        ├── Decomp3DPotential.lean
        ├── Decomp3D.lean
        └── TriangleAndBMM.lean
```

## Quick Start (Lean 4 Verification)

Prerequisites: [`elan`](https://github.com/leanprover/elan) (which automatically
selects `leanprover/lean4:v4.27.0` from `lean/lean-toolchain`), `python3` (for
`lean/scripts/gen_payload_table.py`), `pdflatex` (needed by `make verify` /
`make doc` to compile `lean/FORMALIZATION.tex`), and `md5sum`.

```bash
export PATH="$HOME/.elan/bin:$PATH"

# 1. Fetch precompiled Mathlib 4 .olean cache (avoids building Mathlib from source)
make setup

# 2. Run static hygiene checks, typecheck all 14 Lean files, and build FORMALIZATION.pdf
make verify
```
