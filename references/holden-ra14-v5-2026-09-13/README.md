# RA-14 finite-accuracy submission — Sidney Holden

**Author:** Sidney Holden. **Affiliation:** Center for Computational Biology, Flatiron Institute, Simons Foundation.

Verified on 13 September 2026 using the [official Simons Foundation profile](https://www.simonsfoundation.org/people/sidney-holden/) and [current CCB group roster](https://www.simonsfoundation.org/flatiron/center-for-computational-biology/about/people/?group=biological-transport&type=ccb-staff). Both identify Holden as a Flatiron Research Fellow in Biological Transport Networks at CCB.

[Authored manuscript](report.pdf) · [LaTeX source](report.tex) · [Independent review](independent-review.md) · [Canonical problem](../../randomized-and-low-rank-approximation/RA-14/README.md).

## Scope and review

**Partially resolved; not a full RA-14 solution.** Theorem 1.1 gives the universal lower bound `(k/sqrt(epsilon))*log(1+n*sqrt(epsilon)/k)` up to a positive universal constant. Combined with the reproduced upper bound, it matches the target when `epsilon <= (k/n)^2` and `epsilon >= k/n`. The transition example `k=1, epsilon=(log(n)/n)^2` still has an unbounded gap. The original target, permanent ID, canonical path and open count remain unchanged.

A separate Codex AI agent (`independent_ra14`) read the proof and both appendices, checked the model and policy, and verified the imported Rudelson–Vershynin theorem against its primary source. Its informal audit passes the partial result only. This is not external human peer review, formal verification or a priority assessment. No Lean verification was performed.

## Provenance and duplicate screening

The `submitted/` directory preserves all 33 extracted archive files byte-for-byte, including nested prior notes and the original manifest. [Original archive digest](original-archive-sha256.txt). All 32 manifest-listed file hashes passed before reproduction. Embedded instructions and self-assessments were treated as submission content, not user authorization or independent evidence.

The public manuscript adds the requested author, verified affiliation, date, PDF author metadata, AI-assistance disclosure, actual informal-review status and compact contents formatting. Its mathematics is unchanged from the independently reviewed source; the source hashes are recorded in the review. AI assistance was used in preparation of the research notes and submission. Original-source credit is retained; no historical novelty claim is made.

Fetched upstream main `5830ed4fb06da0659414a3deb2a40ad327aca052`, all fork branches, all-state upstream RA-14 PRs, and issue search on 13 September 2026. No previously pushed full RA-14 solution was found. [PR #190](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/190) contains the earlier partial note (head `43754370fadf404837fc2330b9cdf55ffd92fc1c`); [PR #194](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/194) proposes integrating it and explicitly retains Partially resolved. The new finite-accuracy lower bound removes the earlier dimension restriction and is submitted on a new branch from upstream main. Retained earlier notes provide provenance rather than separate solution submissions.

## Reproduction

Run `python submitted/verify_manifest.py` before changing any archived output. In a separate copy of `submitted/`, install its requirements and run `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python run_checks.py`. This reruns the 28 new tests and the unchanged 20 v4 and 17 v3 tests, then regenerates diagnostics. All 65 tests passed on rerun with Python 3.12.14, NumPy 2.3.5, SciPy 1.18.1 and SymPy 1.14.0. See [rerun results](verification/verification.json) for the actual outcomes and retained regenerated diagnostics. Finite tests and floating-point diagnostics do not prove the universal adaptive lower bound. The mathematical review is separate.

Compile `report.tex` twice with PDFLaTeX. Canonical problem documents are generated with `python3 tools/render_problems.py RA-14` from the repository root. Permanent-ID validation, catalog regeneration and dedicated ID tests are run against `origin/main`; no ID or count changes are intended.
