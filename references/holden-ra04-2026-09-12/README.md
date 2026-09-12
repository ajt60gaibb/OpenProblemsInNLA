# RA-04: Clustered-gap Krylov bounds

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. Current affiliation verified on 2026-09-12 from the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [CCB staff directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff).

**Status: partial results, not a complete solution of RA-04.**

The general iteration bound requested by RA-04 is neither proved nor disproved
in this package. The main report is `RA04_partial_results.pdf` (16 pages).
It contains explicit proofs, identifies its imported convergence theorem,
and separates proved statements from a remaining sufficient interpolation
estimate. No novelty priority or independent peer review is claimed.

## Main mathematical results

Use the notation of RA-04: `t = ceil(k/b)`, `m = k' = bt`, and
`Delta = min_i (sigma_i^2 - sigma_(i+b)^2) / sigma_i^2` over the leading `m`
values. All mathematical results concern exact arithmetic and standard
Gaussian initialization.

For **every admissible input**, the report proves that a sufficiently large
universal constant in

    q = O(( t log(2m/Delta) + log(n/(delta epsilon)) ) / sqrt(epsilon))

is sufficient for the requested spectral-norm, Frobenius-norm, and ordered
right-singular-vector energy guarantees. This differs from the requested
bound by an extra `t log m` term. The proof uses a recursive leave-one-out
identity and a truncated fractional moment, not a lower bound on the raw
monomial Krylov matrix. A second all-input bound replaces the leading term
by `(m-b+1) log(3/Delta)`; either bound may be used.

The **requested iteration order** is proved in the following restricted
regimes: `Delta <= 1/m`; exactly `t` leading levels each repeated `b` times;
arbitrary admissible leading spectra when `t=2`; and the scalar or full-rank
block endpoints `b=1` and `b=k`. These are separate results, not assumptions
that apply to every input. If `rank(A)=m`, the approximation is exactly
optimal almost surely after `t+1` Krylov blocks.

A three-dimensional example disproves a stronger, scale-free conditioning
claim for a raw monomial Krylov matrix. **It is not a counterexample to
RA-04.** The algorithm uses the subspace, not the coordinates of that basis.

The unresolved regime includes arbitrary growing `b,t`, nonzero-width
leading clusters, and `Delta > 1/m`. The sufficient estimate labeled `(IE)`
in the report is not proved there. It is sufficient, not necessary: an
argument using additional Krylov powers could also resolve the question.

## Files

| Path | Contents |
|---|---|
| `RA04_partial_results.pdf` | Main mathematical report, including proofs and sources |
| `src/report.tex` | Editable LaTeX source |
| `tests/exact_checks.py` | Seven groups of exact rational/symbolic identity checks |
| `tests/numerical_checks.py` | Reproducible binary64 and high-precision experiments |
| `results/exact_checks.json` | Exact checks, including 23 general recursive identities |
| `results/numerical_summary.json` | Numerical overview and explicit limitations |
| `results/rbki_metrics.csv` | 117 approximation experiments; all three output measures |
| `results/t2_bound_checks.csv` | 50 tests of the deterministic two-step column bound |
| `results/high_precision_graph_probes.csv` | 12 graph probes at 120 decimal digits |
| `results/raw_conditioning.csv` | Eight raw-conditioning examples at 100 decimal digits |
| `AUDIT.md` | Assumptions, dependencies, and proof-check boundaries |
| `references.json` | Primary-source identifiers and their roles |
| `environment.json` | Versions used for the recorded checks |
| `requirements.txt` | Python dependencies |
| `build.sh` | PDF build command |
| `MANIFEST.sha256` | Checksums for the delivered files other than the manifest itself |

## Reproduce the checks

Python 3.11 or later is required by the pinned NumPy release. A fresh virtual
environment is recommended.

```bash
python -m venv .venv
# Linux/macOS:
source .venv/bin/activate
# Windows PowerShell uses .venv\Scripts\Activate.ps1 instead.
python -m pip install -r requirements.txt
python tests/exact_checks.py --output results/exact_checks.json
python tests/numerical_checks.py --output-dir results
```

The high-precision tests take longer than the binary64 tests. For a quick
numerical check in a separate output directory:

```bash
python tests/numerical_checks.py --skip-high-precision --output-dir quick_results
```

To rebuild the PDF, run `bash build.sh` with a suitable TeX installation.
Required packages include `newtxtext`, `newtxmath`, `amsmath`, `amsthm`,
`mathtools`, `microtype`, `geometry`, `booktabs`, `enumitem`, `xurl`,
`hyperref`, and `bookmark`. The script writes intermediates to `build/`.

## Interpretation of the checks

All seven exact test groups passed. They check finite algebraic identities;
they are not a formal proof-assistant verification of the analytic theorems.
The integer/rational fixtures are not Gaussian samples.

The numerical experiments are selected instances, not a calibrated
high-probability test, a certification of the universal constant, or a proof
of RA-04. High-precision solve residuals are backward residuals, not rigorous
forward-error certificates. The report preserves a finite-precision
exact-rank example that passes an absolute numerical tolerance one step
later than the exact-arithmetic theorem predicts.

## Primary sources

- RA-04 statement:
  https://github.com/ajt60gaibb/OpenProblemsInNLA/tree/main/randomized-and-low-rank-approximation/RA-04
- Chen, Epperly, Meyer, Musco, and Rao, *Does block size matter in randomized
  block Krylov low-rank approximation?*, arXiv:2508.06486v2 / SODA 2026.
  The report explicitly imports their Theorem 3.2, using the right-vector
  convention in their Problem 1.1:
  https://arxiv.org/html/2508.06486v2
- Full bibliographic information and the other comparisons appear in the
  report and `references.json`.

## Repository submission record

Submitted from `RA04_partial_results.zip`. Authorship and verified affiliation were added at the author's request; the mathematical text is unchanged; the contents spacing was tightened to retain the 16-page layout. The supplied `AUDIT.md` is the package's self-audit. The separate [independent agent review](verification/independent-review.md) records the repository review and its scope. This is informal AI-agent review, not external human peer review or formal verification. No Lean verification was requested or performed.

Duplicate screening on 2026-09-12 checked current upstream main, fetched fork branches, RA-04 history, and upstream pull requests; no previously pushed complete RA-04 solution was found. The original target and ID are retained.
