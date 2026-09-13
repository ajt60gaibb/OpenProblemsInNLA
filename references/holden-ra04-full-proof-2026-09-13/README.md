# RA-04: Clustered-gap bounds for randomized block Krylov approximation

**Author:** Sidney Holden — Center for Computational Biology, Flatiron Institute, Simons Foundation.

**Evidence status:** full proof passed an independent informal Codex AI-agent audit; proposed repository status **Solved**. See [submission record](SUBMISSION.md) and [independent review](verification/independent-review.md).

The manuscript claims the exact unrestricted assertion displayed in RA-04. It does not merely extend a restricted cluster-width regime. The additional `t log m` term in the preceding all-input bound is removed. The matrix, Gaussian starting distribution, Krylov space, projected-SVD output, and requested three guarantees are unchanged.

Start with **report.pdf**. Theorem 1.1 states the requested result; Theorem 6.4 proves the new uniform interpolation estimate; Section 7 transfers it to the original algorithm. Sections 3–5 contain the new root-covering, annular, and variational arguments. Section 8 records the principal proof obligations and the evidence level.

## Main estimate

Put `t = ceil(k/b)` and `m = bt`. For a positive leading spectrum with relative `b`-step gap at least `Delta`, let

```math
K_\lambda(H)=[H,\Lambda H,\ldots,\Lambda^{t-1}H],
\qquad
E_{\lambda,H}(x)=[I_b,xI_b,\ldots,x^{t-1}I_b]K_\lambda(H)^{-1},
```

where `H` is an `m`-by-`b` standard real Gaussian matrix. The new theorem is

```math
\Pr\!\left\{
\sup_{0\le x\le\lambda_m}\|E_{\lambda,H}(x)\|_2
\le 2^{24}m^8\eta^{-4}(128e/\Delta)^t
\right\}\ge1-\eta.
```

The dimension and failure probability have fixed polynomial exponents, not exponents growing with `t`. Taking logarithms therefore gives the dependence required in RA-04. The result includes exact repetitions and arbitrary nonzero-width, unaligned clusters under the original `b`-step gap assumption. There is no bound on the leading spectral condition number.

The resulting sufficient iteration count is

```math
q=\left\lceil\frac C{\sqrt\varepsilon}
\left[t\log(2/\Delta)+\log\!\left(\frac n{\delta\varepsilon}\right)\right]\right\rceil.
```

All three outputs are covered: relative spectral error, relative Frobenius error, and the ordered right-singular-vector energy guarantee. The case of zero optimal error is proved separately by exact range recovery at depth `t+1`.

## Proof dependencies

The argument imports two established mathematical results. It uses the real-algebraic conic tube theorem of Bürgisser, Cucker, and Lotz (Theorem 1.1 of arXiv:math/0610270v1) and the deterministic good-start convergence transfer stated as Imported Theorem 3.2 in Chen et al. (arXiv:2508.06486v2). Precise source locations and the transformations applied to those theorems appear in the report and `sources.json`.

Every new interpolation, contour, and descent assertion used in the proof is proved in the manuscript. No conjectural estimate from an earlier package is assumed. The prior work is identified in `provenance.json`; no novelty-priority claim is made.

## Package contents

| File | Purpose |
|---|---|
| `report.pdf` | Complete 14-page mathematical proof claim and references. |
| `src/report.tex`, `src/test_summary.tex` | Editable typesetting source. |
| `PROOF_AUDIT.md` | Self-audit, dependency chain, constants, and failure modes checked. |
| `STATEMENT_CORRESPONDENCE.md` | Comparison with every part of the displayed RA-04 target. |
| `REVIEW_STATUS.md` | Actual review level and proposed repository status. |
| `REPRODUCIBILITY.md` | Test descriptions, execution results, and limitations. |
| `tests/` and `results/` | Exact checks, numerical diagnostics, and recorded outputs. |
| `sources.json`, `provenance.json` | Sources, versions, and hashes of prior artifacts. |
| `SHA256SUMS` | Integrity hashes for the delivered package files. |

## Reproduction

From this directory:

```bash
python -m pip install -r requirements.txt
./reproduce.sh
```

The scripts need Python 3.11 or later. Recorded versions are Python 3.13.5, NumPy 2.3.5, SymPy 1.14.0, and mpmath 1.3.0. A PDF rebuild additionally needs `pdflatex` and the standard LaTeX packages listed in the preamble, including `lmodern`, AMS packages, `mathrsfs`, `microtype`, `booktabs`, `longtable`, `hyperref`, and `fancyvrb`. Run `./build.sh` to rebuild only the report. PDF metadata and floating-point results may vary across environments; byte-for-byte PDF reproduction is not claimed.

## Interpretation

The full exact target passed the separate [independent informal AI-agent audit](verification/independent-review.md), supporting **Solved** under repository policy. This is not external human peer review or formal verification. No Lean was performed. Finite tests do not replace the universal argument. The original self-audit and review-status file below record the package as received; this submission record and the independent report give the updated evidence level.
