# RA-14: Bounds and a spectral-to-PCA reduction

**Author:** Sidney Holden. Biological Transport Networks, Center for Computational Biology, Flatiron Institute, Simons Foundation. See the [submission record](../README.md) for affiliation verification and independent review.

**Status: partial research result, not a complete solution to RA-14.**

The requested problem asks for the optimal number of exact two-sided
matrix-vector products for spectral rank-k approximation, up to universal
constant factors, simultaneously in n, k, and epsilon. This package does not
supply that full characterization. It contains a detailed mathematical attempt,
proved reductions, explicit imported theorem dependencies, and reproducible
numerical illustrations.

Start with **report.pdf** (13 pages, including the cover and contents).
The editable mathematical source is **report.tex**.

## Results in the note

For n >= 2, 1 <= k < n, and 0 < epsilon < 1/2:

- Universal bounds: k <= q_sp <= min{n, ceil(C k log(n)/sqrt(epsilon))}.
  The lower bound handles arbitrary adaptive queries in either oracle direction.
  The Krylov upper bound is imported from Musco and Musco; the n-query cap is
  exact column recovery. Consequently q_sp = Theta(n) for k >= n/2.
- A deterministic postprocessor converts a valid spectral approximation on a
  suitably gapped symmetric input into a strong PCA approximation using at most
  k ceil(10/sqrt(epsilon)) additional vector products. Its proof uses a weighted
  graph inequality and a Fejer-type polynomial. It needs no spectral side
  information in its implementation.
- Combining that postprocessor with the Simchowitz–El Alaoui–Recht PCA lower
  bound gives q_sp = Theta(k log(n)/sqrt(epsilon)) when
  n >= C_* (k/epsilon)^D for universal constants C_* and D. Growing k is allowed;
  the dimension hypothesis is retained and D is not evaluated explicitly.
- An exact rank-padding extraction transfers a bounded rank-one hard family
  without error loss. A sharp example explains why a valid spectral residual
  does not, by itself, imply a strong PCA objective.

The fully quantified, simultaneous finite-parameter lower bound outside these
regimes is missing. In particular, taking the minimum of a dimension-restricted
lower bound and n is **not** justified. The note also does not claim that its
stated global upper bound is sharp in every remaining regime.

## Package contents

| Path | Purpose |
|---|---|
| `report.pdf` | Complete research note, including the precise limitation |
| `report.tex` | Editable LaTeX source |
| `SOURCE_NOTES.md` | Primary sources and exact dependency locations |
| `PROOF_AUDIT.md` | Scope and assumption checks for the principal arguments |
| `STATUS.json` | Machine-readable completion and verification status |
| `src/ra14.py` | Oracle-counted numerical algorithms and validation helpers |
| `tests/test_ra14.py` | 18 unit tests |
| `run_experiments.py` | Recreates the supplied numerical results |
| `results/` | Raw trials, test log, and numerical summary |
| `requirements.txt` | Python dependencies |
| `verify_package.py` | Checks the supplied file checksums |
| `SHA256SUMS` | SHA-256 integrity manifest; excludes itself |

No third-party papers or font files are bundled. The source notes identify the
external theorems used in the proofs. No priority or novelty claim is made.

## Reproduce the checks

Use Python 3.10 or later. The recorded run used Python 3.13.5, NumPy 2.3.5,
and SymPy 1.14.0. From the extracted package directory:

```sh
python verify_package.py
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python -m unittest discover -s tests -v
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python run_experiments.py
```

On Windows, set the two optional thread-count environment variables using the
syntax of your shell, or omit them. No online service or credentials are needed
after the dependencies are installed. The experiment driver writes into
`results/`, replacing the supplied CSV and JSON result files. Check the original
manifest before reproducing the experiments; platform-dependent floating-point
changes can alter regenerated checksums.

To rebuild the PDF with an installed LaTeX distribution:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Standard packages used by the source include amsmath, amsthm, mathtools,
lmodern, geometry, microtype, booktabs, xcolor, hyperref, fancyhdr, and enumitem.

## What the computations establish

The supplied run passed all 18 unit tests. It recorded 270 block-Krylov trials
and 60 warm-start trials. All 60 warm-start trials met their trace targets.
The block-Krylov experiments retained all 19 observed failures at insufficient
chosen depths; no failure was discarded. Twenty scalar grids supplement the
continuous-domain polynomial proof, which is in the report.

These are numerical checks of implementations, identities, constants, and query
accounting. They are not a formal proof, an independent review, or a verification
of a lower bound against every adaptive algorithm. The model in the report uses
exact real arithmetic; the implementation uses double precision and numerical
rank thresholds. The block-Krylov function takes an explicit depth and does not
claim that an experimentally successful depth certifies the universal 99%
guarantee. The warm-start routine requires the spectral promises in Theorem 5.1;
it does not check them using uncharged access to the matrix.
