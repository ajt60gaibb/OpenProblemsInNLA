# PF-04 — Proposed complete solution

## Claimed result

Every real completely positive matrix of order six has a nonnegative factor with at most nine columns. The bound is sharp, including among positive-definite matrices. Thus the manuscript claims **p₆ = 9**.

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation](../README.md).

**Status:** Complete proof passed an [independent informal Codex AI-agent audit](../independent-review.md). Submitted for Solved status under the repository policy. This is not external human peer review or formal verification; exact checks supplement the analytic proof. No Lean verification was performed.

## Start here

Read **PF04_proposed_proof.pdf** (12 pages). Its editable source is **PF04_proposed_proof.tex**. The dependency audit is in **AUDIT.md**, and the primary-source record is in **SOURCES.md**.

The argument uses established theorems rather than claiming to reprove the entire prior theory: the order-five maximum cp-rank, the triangle-free graph bounds, and the corrected exceptional-boundary bounds from Shaked-Monderer’s 2017 paper. Every additional continuous reduction used here is proved in the manuscript.

## The central argument

A nonnegative-inverse shear reduces an edge-minimal positive-definite counterexample to one of three support graphs: K₃,₃, the triangular prism, or K₂,₂,₂ (the octahedron).

The key octahedral lemma bounds the cp-rank by eight when the matrix is orthogonal to a copositive matrix with strictly positive diagonal. It classifies factor columns on the eight triangles and compresses the edge-zero part through a coefficient graph of maximum degree two. Proper octahedral subgraphs then have cp-rank at most eight. For the full octahedral graph, subtracting one rank-one term reaches a remainder of cp-rank at most eight. A finite choice among thirteen positive triangle vectors ensures that a singular full-support endpoint has a suitable positive-diagonal normal. This gives the ninth column without an unhandled degeneracy.

The matrix in `examples/sharp_cp_rank_nine_witness.json` has an explicit 6-by-9 nonnegative integer factor, determinant 36, and cp-rank exactly nine. Its lower bound follows from its nine-edge triangle-free support, not from numerical optimization.

## Reproduce the checks

The verifier requires Python 3.10 or later and only the standard library:

```sh
python3 verification/verify.py --output verification/results.json
```

The supplied result is `PASS`. The program exhaustively checks all 32,768 labelled six-vertex graphs, all 4,096 subgraphs of a fixed octahedron, and all 1,699 triangle-free edge subsets relevant to the zero-counting lemma. It also checks the explicit matrices with exact rational arithmetic, the cross-block determinant identity, and 64 exact examples of the finite vector choice.

These are **finite auxiliary checks**, not a formal verification of the theorem. In particular, the program is not an arbitrary-input cp-factorization solver.

To rebuild the PDF and rerun verification:

```sh
sh reproduce.sh
```

Rebuilding requires a LaTeX installation with the packages used in the source, including `newtx`, `amsmath`, `amsthm`, `mathtools`, `microtype`, `geometry`, `enumitem`, `fancyhdr`, `hyperref`, and `bookmark`. The script writes rebuilt outputs under `build/`.

## Package contents

| File | Purpose |
|---|---|
| `PF04_proposed_proof.pdf` | Complete proposed proof, sharpness witness, and audit discussion |
| `PF04_proposed_proof.tex` | Editable mathematical source with bibliography |
| `AUDIT.md` | Detailed proof obligations and validation limits |
| `SOURCES.md` | Primary sources and precise theorem locators |
| `verification/verify.py` | Standalone exact finite checks |
| `verification/results.json` | Results from the included verifier |
| `examples/*.json` | Exact sharpness and singular-endpoint examples |
| `reproduce.sh` | Verification and PDF rebuild commands |
| `MANIFEST.json` | Machine-readable scope and review status |
| `SHA256SUMS.txt` | Integrity hashes for the package contents |

The archive does not contain copies of third-party papers or font files.
