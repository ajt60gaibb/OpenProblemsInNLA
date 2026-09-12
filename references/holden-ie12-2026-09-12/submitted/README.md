# IE-12: an affirmative exact-real solution with q = 3

**Result.** The accompanying proof gives a randomized algorithm with a deterministic worst-case bound of `O(n^2 / epsilon^3)` scalar operations and `O(n^2)` real-scalar storage. For every input in IE-12, it always returns a nonzero vector and, with probability greater than `0.997`, satisfies

\[
\frac{\|Ax-b\|_2}{\|A\|_2\|x\|_2}\le \frac{5\varepsilon}{8}<\varepsilon.
\]

Here the promised normalization is `||A||_2 = 1`. The result uses exactly the requested **A-only** normwise backward-error metric, not relative residual, forward error, or a metric that also perturbs the right-hand side. Nonsingularity is not needed for the construction, so the theorem also covers normalized singular matrices.

**Start with [`IE12_solution.pdf`](IE12_solution.pdf).** It contains the full 10-page mathematical write-up, all essential proofs, exact-real pseudocode, probability estimates, deterministic operation accounting, and references. Its editable source is [`paper/IE12_solution.tex`](paper/IE12_solution.tex).

Prepared by ChatGPT in this conversation on 12 September 2026. The argument has been checked internally and its components tested, but it has **not** been independently peer-reviewed or verified in a proof assistant. The numerical experiments are illustrations, not substitutes for the proof.

## Why the logarithm disappears

The iteration count is still logarithmic in the dimension. The construction instead makes each repeated matrix product cheaper.

Round the input once to `Q = h Z`, where `Z` is integer, `h = epsilon / (64 sqrt(n))`, and independent unbiased entrywise rounding gives `||Q-A||_2 <= epsilon/8` with high probability. Its total integer coefficient weight satisfies the deterministic bound

\[
W=\sum_{i,j}(1+|Z_{ij}|)\le65n^2/\varepsilon.
\]

For `k = max(1, floor(log_16(n)))`, bounded-weight patterns give exact products with both `Q` and its transpose in

\[
O(n4^k+W/k+n)
\]

operations, after charged preprocessing. This is not an assumption of a constant-size coefficient alphabet: large coefficients are charged to `W` and handled individually. All pattern tables are recomputed and paid for on every product.

A Gaussian-start filter on the rectangular matrix `[Q, -b/||b||]` takes `O(k/epsilon^2)` iterations. The kernel exists by dimension. A clamped conversion handles a zero or tiny last coordinate and preserves the original right-hand side exactly. Since `k 4^k <= 4n`, the full cost is

\[
O\!\left(\frac{k}{\varepsilon^2}
 \left(n4^k+\frac Wk+n\right)+W+k4^k\right)
=O(n^2/\varepsilon^3).
\]

The original-system perturbation certificate is explicit:

\[
\Delta A=\frac{(b-Ax)x^\top}{\|x\|_2^2},\qquad
(A+\Delta A)x=b,\qquad
\|\Delta A\|_2=\frac{\|Ax-b\|_2}{\|x\|_2}.
\]

## Archive contents

| File or directory | Purpose |
| --- | --- |
| `IE12_solution.pdf` | Complete mathematical argument and references |
| `paper/IE12_solution.tex` | Editable LaTeX source |
| `AUDIT.md` | Model, probability, implementation, and edge-case audit |
| `SOURCES.md` | Sources consulted, provenance, and limits of the source search |
| `code/weighted_matvec.py` | Exact generic weighted-pattern product implementation |
| `code/solver.py` | Clearly labeled floating-point solver prototype |
| `code/test_exact.py` | Nine exact component-test groups, standard library only |
| `code/run_experiments.py` | Reproducible numerical illustrations and backend checks |
| `verification/` | Saved test logs, JSON/CSV results, and verification notes |
| `requirements.txt` | Numerical-experiment dependency |
| `build_pdf.sh` | Rebuild the PDF using a local LaTeX installation |
| `SHA256SUMS` | Integrity hashes of every other packaged file |

## Reproduce the checks

Use Python 3.10 or newer. The recorded environment was Python 3.13.5 with NumPy 2.3.5. Run commands from this directory.

Exact component checks require no third-party Python package:

```sh
python code/test_exact.py
```

The recorded run passes all nine groups. The suite covers exact rational forward and transpose products, injective encodings, exhaustive small packings, comparison-based floors, dimension-boundary cost inequalities, rational kernel-filter examples, and zero/tiny-coordinate clamping.

To run the numerical illustrations:

```sh
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python code/run_experiments.py
```

The script writes `verification/experiments.json` and `verification/experiments.csv`. It checks 15 solver instances, five same-draw dense/compressed backend comparisons, six nontrivial catalogue budgets, and 300 rounding trials. The saved run has no failed original-system certificate. The main 15-case suite uses **dense products** for convenience; the theorem's asymptotic bound uses the **compressed product** construction. These experiments are not a speed benchmark.

A small compressed-backend demonstration is also available:

```sh
python code/solver.py
```

## Rebuild the mathematical PDF

Install a LaTeX distribution with `pdflatex`, the New TX text/math packages, and the standard packages used in the source. No font files are distributed in this archive.

```sh
sh build_pdf.sh
```

The script compiles twice in a temporary build directory and writes `IE12_solution.pdf` here. The mathematical PDF was rendered and visually inspected before packaging.

## Exact-real theorem versus the Python demonstration

The theorem counts exact-real scalar operations, including comparisons and square roots; it does not count bits. The paper explicitly implements floor operations through charged comparisons, logarithmic parameters through repeated multiplication, and uniform rounding draws through three permitted standard Gaussian draws. The iteration loop does not need a ceiling primitive. It has a deterministic cap for every possible random outcome, including failure outcomes.

Python cannot literally realize independent exact continuous Gaussian random variables. The solver therefore uses floating-point pseudorandom samples and arithmetic and is not guaranteed stable in finite precision. It may overflow, underflow, or lose accuracy on extreme inputs. It uses a Python ceiling to form its displayed diagnostic step cap; an optional NumPy floor shortcut is also marked. Neither shortcut is assumed in the mathematical operation count.

`backend="compressed"` is the solver default. `backend="dense"` is an experimental alternative. An optional `max_steps` may truncate an experiment, in which case the fixed-time theorem no longer applies. Early exit based on the augmented residual is valid in exact arithmetic and preserves the worst-case bound. The original dense residual is computed only once at the end. Optional spectral-norm diagnostics are excluded from the algorithm proved in the paper.

The exponent `3` and constants are not optimized. This work does not claim a condition-independent forward-error guarantee, a finite-precision theorem, a practical speed advantage, or externally established historical priority.
