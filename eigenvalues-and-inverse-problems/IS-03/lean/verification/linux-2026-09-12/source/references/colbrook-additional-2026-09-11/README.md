# Additional submissions by Matthew J. Colbrook

**Author:** Matthew J. Colbrook.  
**Affiliation:** Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom.  
**Email:** m.colbrook@damtp.cam.ac.uk.  
**Submission and review date:** 11 September 2026.

The author byline is recorded at Matthew J. Colbrook's request. His current affiliation and email were checked against his [official Cambridge homepage](https://www.damtp.cam.ac.uk/user/mjc249/home.html) on 11 September 2026.

## Results and independent verification

The new bundle contains three complete-resolution arguments and one partial bound. Three separate Codex review agents independently checked the complete mathematical arguments and exact target assumptions: one covered both counterexamples, one audited IE-08, and one audited IS-05. Each report records PASS, with the IS-05 verdict explicitly limited to partial progress. These reviews are independent of the original proof-generation session and the submission packaging work.

| ID | Catalog status | Manuscript locator | Independent review |
| --- | --- | --- | --- |
| [IS-03](../../eigenvalues-and-inverse-problems/IS-03/README.md) | Solved | [Theorem 1 and equations (1)–(7)](../../eigenvalues-and-inverse-problems/IS-03/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/IS-03/solution.pdf) | [PASS](verification/reviews/IS-03-review.md) |
| [SP-06](../../eigenvalues-and-inverse-problems/SP-06/README.md) | Solved | [Theorem 1 and equations (1)–(8)](../../eigenvalues-and-inverse-problems/SP-06/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/SP-06/solution.pdf) | [PASS](verification/reviews/SP-06-review.md) |
| [IE-08](../../eigenvalues-and-inverse-problems/IE-08/README.md) | Solved | [Theorem 1, Lemmas 2–12 and the final four proof sections](../../eigenvalues-and-inverse-problems/IE-08/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/IE-08/solution.pdf) | [PASS](verification/reviews/IE-08-review.md) |
| [IS-05](../../eigenvalues-and-inverse-problems/IS-05/README.md) | Partially resolved | [Theorems 1–2 and equations (4)–(8)](../../eigenvalues-and-inverse-problems/IS-05/solution.md) · [PDF](../../eigenvalues-and-inverse-problems/IS-05/solution.pdf) | [PASS](verification/reviews/IS-05-review.md) (partial only) |

IS-03 and SP-06 are negative resolutions by explicit exact counterexamples. IE-08 gives the full stated asymptotic operation and mantissa-precision guarantees, including finite randomness, recursive conditioning, global error, probability and worst-case work. Its proof imports the published Banks et al. regularization theorem, which is credited and was checked by the independent reviewer. IS-05 only sharpens the exponent interval to $17/92\le\alpha_*\le1/2$: the exact exponent and a matching construction remain open.

The original proof drafts were generated in a ChatGPT conversation. This provenance is preserved. Independent Codex-agent verification is not external human peer review or a formal machine-checked certificate. Correctness review does not establish novelty or first-discovery priority. IE-08 is an asymptotic existence proof with conservative constants; the supplied code does not implement the full precision parameters.

## Source integrity and changes

All **30** supplied file checksums were verified. The [bundle manifest](bundle-checks.json) records the ZIP hash, original file hashes and pinned canonical target snapshot `b4123194697bdf6f8f82518c1dd7d6c40a30c2e0`. The original mathematical targets were checked against that snapshot, which remains upstream main at submission time.

The [original Markdown manuscripts](original-manuscripts/README.md) are preserved byte for byte. Every review records the SHA-256 of its full original manuscript, with LF line endings and UTF-8 encoding. The final manuscripts add author, affiliation, date and verification metadata and update draft-status paragraphs. The [proof manifest](proof-hashes.json) identifies mathematical sections whose hashes match exactly between the original and final versions; single-line bibliographic footnote definitions are excluded and display-math delimiters are normalized in these argument hashes, as specified in the manifest. The authored Markdown uses GitHub-compatible dollar display delimiters; this changes only markup, not mathematics. No mathematical argument was changed during packaging.

Three bibliographic updates were made: IS-03's first cited author was corrected from C. Hoover to S. L. Hoover, matching the primary paper; IE-08's inaccurate supplementary §3.3 reference was removed while retaining its correct Theorem 3.6 citation; and IS-05 adds the current Alexeev–Jasper–Mixon version 2 (18 August 2026), §5, Problem 11, which retains the earlier bounds. Original references and dated catalog audits remain visible. Difficulty and importance ratings are retained; difficulty ratings for full resolutions are historical, while IS-05's ratings apply to its surviving target.

## Supporting diagnostics

The [supplied script](verification/check_additional_results.py) was inspected and rerun successfully on 11 September 2026 using Python 3.12.14, NumPy 2.5.0, SciPy 1.18.0 and SymPy 1.14.0. Both [supplied output](verification/supplied-results.txt) and [rerun output](verification/rerun-results.txt) are preserved. Exact certificates and sample counts agree; floating-point residuals can differ slightly between library versions.

The checks cover the exact order-seven derivative certificate and companion trace; the exact Laurent expansion, finite Toeplitz spectrum and Jordan-curve inequalities plus 2,001 curve samples; 872 sign matrices (382 numerically nonsingular); and 300 scalar Newton orbits plus 40 nonnormal matrix diagnostics. None replaces the independent all-orders mathematical reviews or establishes a production implementation of IE-08.

## Documents and submission

Canonical entries retain their original statements and IDs. The three complete resolutions are recorded in [the resolution archive](../../RESOLVED.md); IS-05 remains in the open catalog as Partially resolved. The resulting catalog has **192 open targets** (106 Open and 86 Partially resolved), nine Solved entries and one Solution claimed.

The authored manuscripts use `tools/render_solutions.py` and the shared solution template. The renderer now accepts both dollar-delimited and backslash-delimited display mathematics. The partial manuscript is explicitly headed PARTIAL RESULT. Canonical problem documents use `tools/render_problems.py`; references stay with the dated audit notes on the second page.

```bash
python3 tools/update_catalog.py
python3 tools/render_solutions.py IS-03 SP-06 IE-08 IS-05
python3 tools/render_problems.py IS-03 SP-06 IE-08 IS-05
```

The contribution extends [pull request #6](https://github.com/ajt60gaibb/OpenProblemsInNLA/pull/6), which targets upstream `main`, and uses separate correction-or-resolution issues for these four results. The earlier five authored resolutions and their reviews remain in that PR. A maintainer must accept the PR before upstream main changes.

## Final verification

All eight final PDFs compiled without overfull-box or missing-character warnings using Pandoc 3.11 and XeLaTeX from TeX Live 2023. All 27 pages (19 manuscript pages and eight canonical problem pages) were rendered and visually inspected. Author bylines, affiliations, PDF author metadata, solved/partial notices, rendered mathematics and page bounds passed. Original targets and normalized reviewed mathematical-content hashes match; relative documentation links resolve; repeated index regeneration is idempotent. The earlier five submissions remain unchanged.
