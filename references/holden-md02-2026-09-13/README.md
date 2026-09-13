# MD-02 supporting submission — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.

Verified on 13 September 2026 using the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), which identifies Sidney Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB and records his Edinburgh PhD. Older university listings were not used as current affiliations.

## Scope and independent review

[Manuscript PDF](manuscript.pdf) · [editable source](manuscript.tex) · [retained MD-02 target](../../matrix-discrepancy-and-optimization/MD-02/README.md) · [independent review](independent-review.md).

Theorems 4.1, 5.1, 6.1 and 7.1 prove the exact fixed-point representation, deterministic zero-start Picard convergence, the endpoint expectation equivalence, and all-orders/all-times bounds for the first two iterate moments. Corollary 7.2 proves a first-iterate Gaussian limit. The converged-root estimate is unproved. These auxiliary results do not settle any substantive asymptotic subcase of the displayed target: **MD-02 remains Open**, with no change to the resolution archive or open count.

A separate Codex AI agent (`md02_review`), which did not write or edit the proof, independently audited the argument and passed these supporting results. Its report explains the missing step and policy decision. This is informal automated review, not external human peer review or formal verification. No Lean verification was performed. AI assistance was used for submission preparation and review; no historical priority claim is made.

## Provenance and edits

The `submitted/` directory preserves every extracted file byte-for-byte from `MD02_fixed_point_continuation.zip`, including its manifest and the nested earlier archives. [Original archive digest](original-archive-sha256.txt). Embedded instructions were treated as document content, not user requests. Earlier archives are provenance only, not independently certified submissions or additional resolution claims.

The public manuscript adds the requested author, verified affiliation, date, PDF author metadata and preparation disclosure. The cited primary paper's title and Dmitriev/Kireeva initials were corrected against [arXiv:2502.16227](https://arxiv.org/abs/2502.16227). The mathematical text is unchanged from the independently reviewed source. Original problem and prior-paper attribution are retained.

## Duplicate check and submission

Fetched upstream main at `5830ed4fb06da0659414a3deb2a40ad327aca052` and all fork branches on 13 September 2026. All 33 fork branch versions containing MD-02 retained Open; no previous full solution was found. An all-state upstream pull-request listing (up to 300 entries) searched for MD-02, MD02 and random circulant found no matching prior submission. This is a new branch based directly on upstream main, submitted through a new pull request; no direct push or merge to upstream main is authorized or performed.

## Reproduction

Run from this directory with Python, NumPy and SciPy installed:

```sh
python code/validate.py
python independent-check.py
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
```

[Coordinator rerun](results/validation_summary.json): PASS, 188 enumerated masks and 138 endpoint checks. The [reviewer-written independent check](independent-check.py) also passed 1,520 mask/time cases ([output](results/independent-check.json)). Finite floating-point diagnostics do not prove the missing limit or provide interval certificates. The initial bundled Python lacked SciPy; the successful rerun used an existing environment with the required dependencies, recorded in [runtime versions](results/runtime.json).

Both the manuscript and canonical problem PDF were rebuilt and visually inspected. Permanent-ID validation, index regeneration, all 17 ID safeguard tests, and repository math-format checks passed. The indexes and counts were unchanged.
