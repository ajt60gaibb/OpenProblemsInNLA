# KE-01 partial results — Sidney Holden — 12 September 2026

**Scope:** Partial results only. General KE-01 remains open. [Attributed report](report.pdf) · [TeX source](report.tex) · [Independent review](independent-review.md) · [Canonical target](../../linear-systems-and-elimination/KE-01/README.md).

## Author and verified affiliation

Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation, New York, USA. The [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/), accessed 12 September 2026, identifies Holden as a Flatiron Research Fellow in Biological Transport Networks, CCB. Authorship is recorded at the user's explicit request; the original manuscript disclosed ChatGPT preparation in its PDF metadata. AI assistance was used in submission preparation and review. No external human peer review, novelty claim or formal verification is asserted. No Lean verification was performed.

## Proven scope and remaining question

Theorem 2.1 proves a deterministic sparse CGLS baseline; Corollary 2.2 attains the target bound in four parameter regimes. Theorem 4.1 proves the additive sparsity/outlier bound for explicitly sparse SPD input with an exactly flat eigenvalue tail. Corollary 5.1 treats an exactly flat singular tail with a sum-of-squared-row-support cost, which need not be input sparsity. Propositions 3.1–3.3 disprove specific proposed shortcuts. Proposition 6.1 is conditional on a preconditioner that is not constructed. The arbitrary bounded-tail sparse-input target is not resolved.

## Provenance and eligibility

The supplied `KE01_partial_results.zip` contains only KE-01. Archive SHA-256: `dc92ac9558ca0d56f5a53ad4ac947ff25a877516c50e91d7e611ba7cff13ad82`. All 13 entries of its manifest were verified. The unchanged extracted package is retained in [submitted](submitted/README.md). Embedded instructions were treated as document content, not user authorization. The attributed report changes only front matter and provenance; its mathematical body is unchanged.

This new branch starts at upstream main `f41f1f9`. Both remotes were freshly fetched; all fetched histories touching KE-01, both repositories' all-state KE-01 PR searches, and upstream's all-state issue search found no previously pushed full KE-01 solution or related issue. This is a bounded repository duplicate check, not a publication-priority certificate. Original permanent ID, canonical path and mathematical target are retained.

## Reproduction and review

The separate Codex agent `/root/ke01_independent_review` reviewed the manuscript and target independently and reran the exact tests. Its report records the verdict and limitations. Reproduced output is in [verification](verification/); archived results remain under `submitted/results/`. The verifier uses SymPy 1.14.0 and can be rerun from this directory with `python code/verify_exact.py --out reproduced_results`.

The finite checks cover 66 CGLS cases, 209 Chebyshev inequalities, 8 flat-tail cases, 28 inner-PCG iterates, 5 Gram-fill cases, 9 Nyström cases and 3 row-sketch cases. They test examples and identities, not the asymptotic bound or universal success probability.

The report was built with two pdflatex passes. Canonical documents and catalog indexes were regenerated with repository tools; permanent-ID validation, safeguard tests and math-format checks were run. PDF pages were rendered for visual inspection.
