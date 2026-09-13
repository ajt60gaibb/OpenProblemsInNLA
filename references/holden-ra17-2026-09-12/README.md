# RA-17: Exact Cases and Certified Bounds

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation.

Affiliation verified on 12 September 2026 from the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), which lists Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks, CCB. See the [submission record](SUBMISSION.md) and [independent review](independent-review.md).

**Status: PARTIAL. This archive does not give the requested all-dimension classification.**

The principal exact result proved in the manuscript is

\[
\mu_{\mathbb R}(4,1)=11.
\]

The lower bound rules out ten measurements by a characteristic-class obstruction on the real Grassmannian of two-planes in four-space. The upper bound is certified from both versions of Xu's eleven measurement matrices, with exact rational arithmetic. A normalization chart alone is not used: the projective hyperplane at infinity is checked separately.

Start with **`writeup/RA17_exact_cases_and_bounds.pdf`**, a 17-page manuscript. Its editable LaTeX source is included. Section 5 gives the short topological lower-bound proof; Section 6 explains the algebraic certificates; Section 9 records the remaining gaps.

## Results and scope

The manuscript also supplies an explicit anti-diagonal construction attaining the universal upper bound `4*d*r - 4*r*r`, general Pontryagin–Euler and Stiefel–Whitney lower bounds, an odd-determinantal-degree exactness criterion, Hurwitz–Radon constructions, and exact corank-one families. In particular, the arguments give `mu_R(8,3)=56` and `mu_R(24,11)=568`.

They do **not** prove that the characteristic-class necessary conditions are sufficient. For example, the bounds established here leave

- `138 <= mu_R(12,5) <= 139`, and
- `246 <= mu_R(16,7) <= 247`.

These are gaps in the arguments supplied in this archive, not a claim that the intervals are the best bounds anywhere in the literature. No priority claim is made for the mathematical arguments. The topology has passed an independent informal AI-agent audit, but has not been formalized in a proof assistant or externally peer reviewed.

## Archive contents

| Location | Contents |
|---|---|
| `writeup/` | Proofs, source audit, exact families, limitations, references; PDF and LaTeX |
| `code/verify_xu.py` | Regenerates the two-chart certificates from the measurement rows |
| `code/rref.cpp` | Small exact rational RREF implementation using GMP |
| `code/constructions.py` | Explicit anti-diagonal measurements, Hurwitz spaces, and Xu–octonion lifts |
| `code/bounds.py` | Computes proved intervals, with an explicit exactness flag |
| `code/test_constructions.py` | Exact identity, dimension, rank, and parity tests |
| `certificates/` | Measurement matrices, rational kernel bases, multiplication matrices, eliminant coefficients, and Sturm signs |
| `results/` | Executed verification logs, regenerated certificates, and bounds through dimension 16 |
| `SOURCES.md` | Primary-source inventory and the two source discrepancies |
| `SHA256SUMS` | Integrity manifest for the delivered files, before regeneration |

## Reproduce the checks

Python 3.10 or later and SymPy are required. The delivered checks were executed with Python 3.13 and SymPy 1.14.0. The exact SymPy version is pinned in `requirements.txt`.

From the archive root:

```sh
python -m pip install -r requirements.txt
python code/verify_xu.py --variant both --backend sympy
python code/test_constructions.py
python code/bounds.py --max-d 16
```

The pure-SymPy backend needs no C++ compiler. For faster rational row reduction, the default backend uses `g++` with C++17 support and GMP development headers/libraries:

```sh
python code/verify_xu.py --variant both
```

The verifier compiles its helper into a temporary directory. It regenerates the cubic minors, computes the rational row reductions, builds the characteristic polynomial, performs the Sturm count, and checks the infinite chart. It compares the recomputed multiplication matrix, polynomial, and signs with the delivered reference data. A failed check raises an error rather than reporting success. `--output PATH` changes the destination of regenerated results; by default it writes to `results/`.

The delivered `verification.log` records both variants using GMP; `independent_sympy_check.log` records an additional independent row-reduction computation of the printed-paper variant using SymPy. The backend independence does not mean that every later polynomial operation uses a separate implementation: both backends use SymPy for the characteristic polynomial and Sturm sequence.

### Expected certificate checks

| Check | Printed-paper variant | Website variant |
|---|---:|---:|
| Measurement rank | 11 | 11 |
| Affine Macaulay matrix | 240 by 126 | 240 by 126 |
| Affine rank | 106 | 106 |
| Necessary eliminant degree | 20 | 20 |
| Sturm variations at negative / positive infinity | 10 / 10 | 10 / 10 |
| Real roots | 0 | 0 |
| Infinite-chart Macaulay matrix | 160 by 56 | 160 by 56 |
| Infinite-chart rank | 56 | 56 |

The construction tests check identities in the coefficients, not randomly sampled matrices. They do not certify the separate topological arguments. `bounds.py` is an implementation of proved bounds, **not** a real-algebraic feasibility solver or a full solution of RA-17. Its partition enumeration has a configurable limit; skipped enumerations are explicitly marked.

## Data conventions

The measurement matrix `W` is 11 by 16 and acts on row-major vectorizations. In this convention, its rows are simultaneous transposes of Xu's displayed source matrices, which preserves rank and uniform injectivity. The five kernel parameters correspond to `(x34,x41,x42,x43,x44)`.

The manuscript names these parameters `(a,b,c,z,t)`. The JSON certificates and internal symbolic calculation name the fourth parameter `d` rather than `z`; that symbol is **not** the ambient matrix dimension. Exponent tuples are always ordered by these four affine parameters, with the homogenizing parameter last where applicable.

The printed-paper and website variants differ in precisely two entries. Both are included and checked; neither is silently substituted for the other. See `SOURCES.md` and manuscript Section 6.1.

## Build the manuscript and check file integrity

A standard TeX installation with `pdflatex`, AMS packages, `lmodern`, `microtype`, `hyperref`, `xurl`, `enumitem`, and `listings` can build the PDF:

```sh
cd writeup
pdflatex -interaction=nonstopmode -halt-on-error RA17_exact_cases_and_bounds.tex
pdflatex -interaction=nonstopmode -halt-on-error RA17_exact_cases_and_bounds.tex
```

Before modifying or regenerating files, verify the delivered manifest from the root:

```sh
sha256sum -c SHA256SUMS
```

On systems providing `shasum` instead, use `shasum -a 256 -c SHA256SUMS`. The manifest is an integrity check, not part of the mathematical proof. No third-party source PDFs or font files are distributed in this archive.
