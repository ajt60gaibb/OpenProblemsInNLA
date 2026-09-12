# MF-21 affirmative resolution - 12 September 2026 (UTC)

**Author:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.

The [complete proof](../../matrix-functions-and-stability/MF-21/solution.md), Theorem 1 and Sections 2–5, establishes all three original assertions for every integer `m >= 3`. One common smooth coefficient family gives the uniform expansion through order `2m-1`, the order-`2m` expansion above the prescribed squared-logarithm index cutoff, and failure of the order-`2m` expansion uniformly over all indices. The symbol, grid, quantifiers, canonical path and original statement are retained.

[Proof PDF](../../matrix-functions-and-stability/MF-21/solution.pdf) · [Standalone proof TeX](../../matrix-functions-and-stability/MF-21/solution.tex) · [Canonical entry](../../matrix-functions-and-stability/MF-21/README.md).

## Mathematical review and source binding

The separate [independent Codex-agent mathematical audit](independent-review.md) returned PASS for the complete all-`m`, three-part proof with no mathematical corrections. The report identifies the drafting and reviewing agents and addresses the coalescing characteristic roots, normalized boundary determinant, upper-endpoint cancellation, exact eigenvalue indexing, common coefficient family, kernel normalization and dominated trace limit. Substantial AI assistance is disclosed. This is informal automated review, not external human peer review or formal verification.

The exact frozen [reviewed source](reviewed-proof.md) is 19,393 bytes with SHA-256 `98eb74a858ad3d2bf5fd0055a92d9c96b9a5e4f4f531972cd429462acb2b44f5`. The final public manuscript has SHA-256 `6e1bb10bb2ccfe1311775a6d24ca292113036867e080185741ef4f5d5b8174aa`. The [editorial conversion record](editorial-conversion.json) contains their full difference and the three parenthesis/math-delimiter repair groups. After those recorded repairs, the mathematical core, Sections 1–5, is byte-identical (16,143 bytes; SHA-256 `e75264cb480d17a2c32e6876b5949befa70bbf991f6391720cfcb0d65b799012`). The [independent publication comparison](publication-markdown-review.md) also passed; the remaining changes concern the author/review wrapper and replacement of preliminary private-work status by the completed review and eligibility records.

The [original target snapshot](canonical-statement.md) is unchanged from upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. The original Statement-through-history suffix is preserved byte-for-byte in the live entry. Relative navigation links in the frozen snapshot are historical; use the canonical-entry link above for current navigation.

The original [draft manifest](frozen-manifest.json), [supporting manifest](supporting-manifest.json), and [independent-review manifest](independent-review-manifest.json) are retained as historical records. Their `RESULT.md` is archived as `reviewed-proof.md`, and the reviewer's identical copy remains `reviewed-candidate.md`. The canonical snapshot is available under both `canonical-statement.md` and the reviewer's original `canonical-target.md`. The unchanged signed report is available as both `independent-review.md` and `independent-math-review.md`, preserving its original manifest entry. The preliminary pending-review text in the frozen draft and manifest is superseded by the signed PASS report. The final package [manifest](manifest.json) records the published filenames and hashes.

## Prior results and eligibility

Barrera, Böttcher, Grudsky and Maximenko retain credit for Conjecture 8.4 and the fourth-order special case. The cited later authors retain credit for the seven-diagonal and local expansion results. The [source notes](source-notes.md) and separate [source/scope review](source-scope-review.md) identify the primary publications, versions, theorem locations and limits of the later-work search.

The substantive external Toeplitz input is the classical uniform inverse-kernel convergence recorded in [Böttcher–Widom, arXiv:math/0412269](https://arxiv.org/pdf/math/0412269), printed page 4, the paragraph immediately before equation (13); formula (5), printed page 2, supplies the kernel. The note and audit explicitly check the ceiling-cell convention, the trace normalization and why essential-uniform convergence controls the diagonal here. The boundary determinant estimates, coefficient construction and trace contradiction are derived in the submitted proof. Finite exact calculations are supplementary and do not replace these analytic arguments.

The [public-network audit](public-audit/README.md) at 2026-09-12 03:37:45 UTC discovered six public repositories and 48 branch heads. It read 232 selected text blobs, 175 issue/PR/comment bodies, and 32 review bodies from 38 review endpoints. Every returned canonical MF-21 page was Open; no competing full solution was found in the selected documents or discussions. The source/scope search likewise found no existing resolution of all three parts for every `m >= 3`. The archived snapshot contains sanitized metadata and fingerprints; retrieved discussion bodies and third-party documents are not republished. A bounded public search does not certify novelty or exclude private, deleted, unpublished or later-posted work.

## Reproduction and document verification

Run from the repository root:

```sh
python3 references/stepaniants-mf21-2026-09-12/exact_check.py
python3 references/stepaniants-mf21-2026-09-12/exact_algebra_check.py
python3 references/stepaniants-mf21-2026-09-12/build_solution.py
python3 tools/render_problems.py MF-21
python3 tools/validate_problem_ids.py --base-ref origin/main
python3 tools/update_catalog.py --base-ref origin/main
python3 -m unittest discover -s tests -p 'test_problem_ids.py' -v
python3 -m unittest discover -s tests -p 'test_problem_statuses.py' -v
python3 references/stepaniants-mf21-2026-09-12/check_submission.py
```

Both mathematical checkers use only the Python standard library. The author's checker verifies 14 exact boundary/Laplace cases, 20 Green-kernel/trace orders and 32 circulant-compression cases; its sole packaging change replaces `RESULT.md` by the unchanged archive name `reviewed-proof.md`. The [reproduced author output](exact-check.json) binds the adapted checker. The unchanged [original output](original-exact-check.json) retains its original checker hash for the historical supporting manifest. The separately written reviewer's checker verifies ten Gaussian-rational determinant cases and twelve rational beta-integral identities; its [output](exact-algebra-output.json) and source are unchanged. These finite checks support the algebra and transcription, not the all-`m` analytic theorem by themselves.

The proof builder uses Pandoc and XeLaTeX; set `PANDOC` if the executable is not on PATH. Both exported TeX sources compile standalone. The final [verification record](verification.json) records the required 17 permanent-ID tests and three status tests, both published-base validations, exact-checker reruns, preservation and conversion checks, and author/affiliation/contact-email checks. All 260 proof formulas and 34 canonical formulas match the corresponding TeX in order. The only renderer change removes MF-21's forced reference-page break, reducing its canonical PDF from three pages to two without changing source content or another problem's rendering behavior.

The final seven-page proof PDF was visually inspected on every page by a separate agent; the coordinating agent inspected both final canonical PDF pages. The [packaging audit](packaging-review/MF-21-packaging-review.md) records its checks separately from the mathematical audit and visual inspection. The [last public-head refresh](packaging-review/head-refresh.json) found the six-repository, 48-head inventory unchanged at 03:56:04 UTC on 12 September 2026, with upstream main still at the recorded base.

`Solved` is proposed under the repository's independent-informal-audit rule. Inclusion in upstream `main` requires maintainer review and merge of the new pull request.
