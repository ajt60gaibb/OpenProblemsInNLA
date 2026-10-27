# RE-06 submission record

**Author:** Sidney Holden  
**Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.  
**Verified:** 13 September 2026, from the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current group directory](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff), which identify Holden as a Flatiron Research Fellow in Biological Transport Networks.

[Attributed manuscript](../../randomized-and-low-rank-approximation/RE-06/solution.pdf) · [TeX](../../randomized-and-low-rank-approximation/RE-06/solution.tex) · [Independent review](independent-review.md)

The user supplied `RE-06_solution.zip` and requested authorship attribution. `submitted/` retains the original archive contents, including its original manifest, self-audit and numerical logs. Its self-audit is not the independent review. The attributed version changes authorship and review disclosure only; the mathematical argument is unchanged. Repository preparation used Codex assistance. No Lean verification or external human peer review is claimed.

The separate Codex AI-agent reviewer audited the full theorem against the canonical target and independently recomputed parameter and probability bounds. Theorem 1.1 and Sections 2–6 settle the exact-real, query-only, fully nonadaptive target affirmatively with C = 4,000,000 and b = 0. Numerical tests supplement the proof and use floating point; experimental widths do not inherit the universal theorem guarantee.

Duplicate check: refreshed upstream main and all fork branches and searched upstream PR history (all states, including the submitting user's descriptions); no prior full RE-06 solution was found. The branch begins at upstream revision `5830ed4`. Original ID, path, target and prior references are retained.

Archive SHA-256: `9bfe8e35805e4fff7c729d818e3a39ea46ae20566b71c24a0dd683381886d6f2`.

## Reproduction and validation

On 13 September 2026, the integration run passed all 11 supplied unit tests and reran `code/verify.py` using Python with NumPy 2.3.5 and SciPy 1.17.0, with `OPENBLAS_NUM_THREADS=1`. See [unit-test log](unit-tests-rerun.txt), [verification log](verification-rerun.txt) and [rerun data](rerun-results/). The original archive results remain unchanged. The 640 end-to-end trials again returned optimal candidates; this remains supplementary numerical evidence.

Permanent-ID validation against `origin/main` and `upstream/main`, catalog regeneration, all 17 permanent-ID tests, and repository math-format checks passed. Both PDFs were rebuilt and all 14 pages visually inspected without layout defects. No Lean checks were run.
