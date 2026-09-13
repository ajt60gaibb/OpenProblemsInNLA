# Canonical PDF publication review: PRs 187, 192, and 193

**Verdict: PASS for all three canonical problem PDFs. No publication blocker found.**

Reviewed on 12 September 2026 from read-only exact-head checkouts:

| PR | Head | Canonical PDF | Pages inspected |
| --- | --- | --- | ---: |
| 187 | `94e8ae24e4c10e79d8b3502101ee4a0287506f81` | `matrix-inequalities-and-norms/MI-03/problem.pdf` | 3 of 3 |
| 192 | `3fc8bde9c014d22575bbfb73c644c5ce0c492d29` | `linear-systems-and-elimination/IE-23/problem.pdf` | 3 of 3 |
| 193 | `f73edd6c6562a78d1c4f56fdc4c1c75dac9ace4a` | `intervals-and-absolute-value-equations/IV-06/problem.pdf` | 3 of 3 |

I used the PDF skill, inspected metadata with `pdfinfo`, rendered each entire PDF through Poppler at 115 dpi, and visually examined every rendered page. Scratch renders are in `/private/tmp/nla-lean-publication-pdf-review/`. The corresponding canonical READMEs were read to check attribution and publication scope. No PDF or source was altered.

All nine pages have readable mathematical symbols, unclipped equations and code blocks, intact reference entries, readable theorem-export lists, consistent canonical headings/IDs and page numbers, and visible source/evidence links. There are no broken glyphs, overlapping text, hidden mathematical lines, or materially misleading page breaks. Historical dated audits remain visibly separated from the new resolution and Lean-evidence sections.

## MI-03 / PR 187

The PDF identifies the original odd-summand question and preserves its quantifiers over all dimensions and complex contractions. The new formalization summary accurately advertises the stronger all-`k >= 2` least-constant and actual-infimum claim, including the odd case. It distinguishes genuine CFC moduli and operator norms from informal shorthand. The original theorem is credited to Matthew J. Colbrook; George Stepaniants is separately credited for AI-assisted formalization; Bourin and Lee retain original conjecture and prior-bound credit.

The document states that LeanCert audits kernel trust and that there is no numerical interval certificate. It explicitly keeps the extra three-dimensional Hermitian extremizers and rank classification outside the listed exports. It distinguishes the historical informal proof review from subsequent Lean verification and does not present operational roles as extra mathematical referees.

## IE-23 / PR 192

The PDF clearly distinguishes the manuscript's all-`p` statements from the formal negative resolution via the rational example at `p=4`. The latter suffices to refute the preserved universal uniqueness conjecture. It states actual induced suprema and global minimality over every complex right inverse, while retaining the original exclusion of the separate product objective and endpoints. The displayed fourth root and nonzero-input supremum are legible.

Colbrook retains mathematical authorship, Stepaniants receives formalization credit, and Dokmanić and Gribonval retain original example/question credit. The document expressly leaves the all-`p` minimizer classifications and higher-dimensional families in their manuscript/informal-review scope. It accurately states that the proof uses exact algebra and no numerical interval certificate.

## IV-06 / PR 193

The PDF preserves the complete independent-entry real-eigenvalue component-count question, including singleton entry intervals and no symmetry/all-real-spectrum assumptions. The new section advertises at least four genuine components in dimension three and the full universal negation. It explicitly uses actual `ConnectedComponents` and `Cardinal` and excludes claims of exactly four components, all endpoints, or a replacement general bound.

Colbrook, Stepaniants, and the original-question authors have distinct and appropriate credit. The LeanCert contribution is stated precisely: the explicit kernel sign certificate for `-18 < 0`, after exact universal affine bounds; topology and cardinality complete the proof. No approximate eigenvalue or interval-subdivision claim is made.

This publication review does not independently repeat CI, dependency authentication, author-affiliation research, or the complete MI-03/IE-23 mathematical proof reviews. Those remain with the coordinating review. IV-06 received the separate complete source cross-review recorded at `/private/tmp/nla-pr193-cross-review.md`.
