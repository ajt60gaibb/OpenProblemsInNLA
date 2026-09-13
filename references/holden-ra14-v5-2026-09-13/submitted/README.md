# RA-14 — Finite-Accuracy Lower Bounds (continuation 5)

**Status: PARTIAL.** This archive contains a new universal lower-bound argument and new matching regimes. It is **not** a complete solution of the repository's simultaneous finite-parameter problem. The manuscript is unreviewed; no mathematical priority, independent peer review, or proof-assistant verification is claimed.

Start with **report.pdf** (18 pages). **report.tex** is the editable source. **PROOF_AUDIT.md** records the exact dependencies and the points that require mathematical review. **CLAIMS.json** separates proved-in-the-note claims, imported material, and the unresolved characterization.

## The new result

For every integer `n >= 2`, `1 <= k < n`, and real `0 < epsilon < 1/2`, the note gives a proof that a universal `c > 0` satisfies

```text
q_sp(n,k,epsilon) >= c * (k/sqrt(epsilon))
                        * log(1 + n*sqrt(epsilon)/k).
```

Here `q_sp` counts individual exact products `A*x` or `A.T*x`. Queries may be arbitrary measurable functions of all previous replies and independent randomness. For every input, an orthonormal output `Z` must satisfy

```text
||A(I - Z Z.T)||_2 <= (1 + epsilon) sigma_{k+1}(A)
```

with probability at least 0.99. The new lower bound has no dimension-growth restriction. Its constant is universal but not optimized or numerically evaluated.

Together with the upper bound from the preceding packages, reproduced in Appendix B, the result gives

```text
max{k, c F} <= q_sp <= min{n, ceil(12000*k/sqrt(epsilon)*log(e*n/k))},
F = (k/sqrt(epsilon))*log(1+n*sqrt(epsilon)/k).
```

In particular, the note establishes matching universal-constant bounds in both of the following regions:

* `epsilon <= (k/n)^2`: `q_sp = Theta(n)`.
* `epsilon >= k/n`: `q_sp = Theta(min{n, k/sqrt(epsilon)*log(e*n/k)})`.

The previously explicit gap at `k=1, epsilon=1/n` is closed:
`q_sp = Theta(sqrt(n)*log(n))` for `n > 2`.
For every fixed positive `delta`, matching bounds also follow throughout
`epsilon >= (k/n)^(2-2*delta)`, with constants that may depend on `delta`.
Those constants are not claimed to remain universal as `delta` approaches zero.

## What is not solved

At `k=1` and `epsilon=(log(n)/n)^2`, this package still gives only

```text
Omega(n*log(log(n))/log(n)) <= q_sp <= n.
```

The factor `log(n)/log(log(n))` is unbounded. Thus neither the new lower expression nor the old capped upper expression is asserted to be optimal for all parameters. The archive must not be represented as a full RA-14 solution or used to mark the problem solved.

## The argument

The hard input is `M = I - H/(100*n)`, where `H` has an exact hidden `k`-dimensional kernel. Its law is obtained by multiplying the density of a singular Gaussian Wishart matrix by `pdet(H)^(nu/2)` and normalizing. The nonzero spectrum is a rectangular Gaussian Gram spectrum with `n+nu` degrees of freedom.

The proof derives the exact conditional kernel law after arbitrary adaptive queries. In Schur-complement coordinates it is proportional to

```text
det(I + Q.T*K*Q)^(nu/2)
```

on a Grassmann manifold. An integration-by-parts lemma bounds its regularized second moment. A log-determinant potential of the hidden-kernel overlap consequently obeys an expectation budget of `4*nu*T/n` for `k <= n/8`, `T <= n/4`.

The Rudelson–Vershynin least-singular-value theorem provides a finite-dimensional spectral gap; it is the only imported non-elementary probabilistic theorem in this new argument. The earlier spectral-to-PCA postprocessor is proved again in Appendix A, with every additional query charged. Proposition 9.3 retains its overhead explicitly; Section 10 makes all parameter choices and fallback cases explicit to obtain the all-parameter lower bound.

## Contents

| Path | Contents |
| --- | --- |
| `report.pdf`, `report.tex` | Mathematical write-up and editable LaTeX |
| `PROOF_AUDIT.md` | Definitions, proof dependencies, caveats, and audit checklist |
| `CLAIMS.json`, `STATUS.json` | Machine-readable scope and completion status |
| `src/wishart_geometry.py` | Typed numerical components and oracle-counted diagnostic strategies |
| `tests/test_geometry.py` | New component tests |
| `run_checks.py` | Current tests, unchanged earlier suites, and diagnostic reproduction |
| `results/` | Actual test logs, all diagnostic rows, and verification metadata |
| `sources/` | Primary-source inventory and exact dependency notes |
| `prior/` | Original v4 PDF and ZIP, preserved byte-for-byte; the ZIP contains earlier rounds |
| `verify_manifest.py`, `MANIFEST.sha256` | File-integrity check for this distributed snapshot |

## Actual checks

All **28 new tests**, **20 unchanged v4 tests**, and **17 unchanged v3 upper-bound tests** passed: **65 tests in total**. Diagnostic output contains 72 kernel-geometry case rows, six angular summary rows based on 60,000 importance-sampling draws, and 432 legal adaptive runs producing 8,208 path rows. The individual angular draws are reproducible from the recorded code and seed but are not included as separate rows. There are also 1,026 empirical-expectation rows and 83 finite-parameter scale comparisons.

The largest pseudodeterminant log-identity error in the geometry trials was below `1.92e-13`. These calculations test identities, constants, and finite implementations. They **do not prove** a universal lower bound against all adaptive algorithms, independently certify the new Grassmann lemma, or numerically determine its universal constants. Floating-point calculations are distinct from the exact-real model.

## Reproduction

Use a fresh extraction. Check integrity before regenerating output:

```bash
python verify_manifest.py
python -m pip install -r requirements.txt
OPENBLAS_NUM_THREADS=1 python run_checks.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`run_checks.py` extracts the preserved v4 ZIP into a temporary directory and runs its v4 and v3 suites without modifying their assertions or their original archives. It writes all new logs and results into `results/`; this intentionally changes the snapshot hashes. Recompiling the PDF can also change its binary hash. A manifest mismatch after reproduction is not, by itself, a mathematical or test failure.

The recorded numerical environment was Python 3.13.5, NumPy 2.3.5, and SciPy 1.17.0. SymPy is included in the requirements for the unchanged earlier component suites. No code here estimates an arbitrary matrix norm for free or gives an algorithm access to the hidden kernel: such quantities are confined to validation after the oracle queries have been chosen.

No repository files have been changed.
