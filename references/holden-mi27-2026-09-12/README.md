# MI-27 — solution with the optimal coefficient one

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.


## Result

For all positive definite complex matrices A and B with tr(A+B)=1,

    ||[B, log(A+B)]||_1 <= -tr(A) log(tr(A)) - tr(B) log(tr(B)).

The coefficient **one is optimal**, already for strictly positive definite 2-by-2 matrices.

The proof combines a uniform unitary Lipschitz estimate for matrix positive parts with Frenkel's published relative-entropy representation, in the form of Hirche and Tomamichel. The positive integral kernels have total mass exactly equal to the required binary entropy. The supplied pack's strict-positive sharpness family gives the matching lower bound on any universal coefficient.

## Files

| File | Contents |
|---|---|
| `solution.pdf` | Seven-page proof, sharpness argument, references, and appendices. |
| `solution.tex` | Complete LaTeX source; no external assets or bibliography processor needed. |
| `solution.md` | Markdown proof of the same theorem and sharpness, with source links. |
| `references.bib` | Machine-readable bibliography. |
| `audit.md` | Explicit checks of the main possible proof gaps and normalization pitfalls. |
| `provenance.md` | Source versions, input-archive hashes, and attribution of the supplied findings. |
| `provenance/input_MI27_result.md` | Unchanged MI-27 result from the uploaded pack. |
| `verification/verify.py` | Deterministic symbolic and numerical consistency checks. |
| `verification/results.json` | Saved test results, tolerances in the script, software versions, and seed. |
| `verification/run.log` | Output of the verification run. |
| `verification/requirements.txt` | Python package versions used for the saved run. |
| `SHA256SUMS.txt` | Integrity hashes of all other archive files. |

## Reproduce the verification

From this directory, using Python 3.11 or later:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r verification/requirements.txt
python verification/verify.py --output verification/results_rerun.json
```

On Windows, activate the environment with `.venv\Scripts\activate` instead. The saved run used Python 3.13.5. No network is used by `verify.py`; package installation is the only step that may require network access. The script exits nonzero if a check fails.

The saved run passed all nine exact symbolic identities; 300 random positive-part derivative checks; five eigenvalue-crossing checks and four near-saturation checks; seven high-precision kernel-mass checks; 20 matrix pairs testing each of three integral formulas; 84 matrix-inequality checks through dimension 32; 96 finite-time entropy checks; 32 entropy-derivative checks; and eight high-precision sharpness-family evaluations.

The largest discrepancy in the integral-identity tests was approximately **1.07e-14**. These tests are consistency checks, **not a proof** of the universal inequality. The proof is analytic and does not depend on any optimization output or numerical assertion.

## Rebuild the PDF

With a standard LaTeX installation including the packages listed in the source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
pdflatex -interaction=nonstopmode -halt-on-error solution.tex
```

The bibliography is included directly in `solution.tex`; `references.bib` is supplied for reuse. LaTeX-created auxiliary files need not be retained.

## Scope

This is a complete analytic proof write-up using an explicitly cited published theorem, not a proof-assistant formalization or an independently refereed paper. No claim of historical publication priority is made. The public problem page and primary papers were read through the web; no GitHub connector was used and no repository was modified.

## Submission and review

See [authorship, verified affiliation and duplicate screening](provenance.md#repository-submission-record-12-september-2026) and the [independent informal AI review](verification/independent-review.md). The supplied `audit.md` is the original self-audit and is distinct from the independent review. Prior partial findings are credited in Section 5 and provenance. No Lean verification or external human peer review is claimed.
