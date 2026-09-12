# RA-19 publication-conversion review

Reviewer: coordinating Codex agent `/root`, 12 September 2026 UTC (11 September locally).

**PASS.** I independently inspected the complete frozen publication conversion after the author's packaging work. This check is separate from my [mathematical audit](RA-19-root-math-review.md) and the [independent mathematical review](independent-review/review.md). It checks preservation, presentation, attribution and repository integration; it does not constitute formal verification or external human peer review.

## Exact reviewed artifacts

The six canonical files below are relative to `randomized-and-low-rank-approximation/RA-19/`. They are byte-identical to the packager's final handoff. No mathematical or PDF amendment was required by this review.

| Artifact | SHA-256 |
| --- | --- |
| README.md | `514c8179fcc5b44a8d7517e5bc6c650722352a58e98d0c6a490669b97d0bd734` |
| solution.md | `edbbf77a2227e6cf99a30cc2eea2ce170cd7d6346b2cc9e0b5c7ceb9fe06c94b` |
| solution.tex | `f02c9be73ad9b5b6f31363190b9d977f6b345fd73c23e5b85b7bf387856ec3d6` |
| solution.pdf | `7b08715d6f3a2506a00a7a27f4a8ac9712b7eaf0952622429ef5ffaded9340fc` |
| problem.tex | `9f339368dabb5a4e6c37faaf3ada22bd19f4c7b84b745b9dc4ccbc95b08f66cd` |
| problem.pdf | `22b3b4016a31293a279dd2fcf02a5a9af37d7dad8cd8b82b592eaba09772f190` |

## Source and exact-target preservation

I independently extracted Sections 1-6 from the original frozen proof and the canonical solution Markdown, removing only explicit `Needspace` and `nopagebreak` layout directives from the latter. Their 17,059 bytes are identical, SHA-256 `9b7c3293548e04b0dc474ac6de34499b398e07d2a98500fa2c7ba892c6981cb5`. All 281 ordered mathematical expressions agree with the standalone TeX after whitespace normalization. I also read the rendered mathematics and explanatory paragraphs, including the simple-eigenvalue argument, reducedness lemma, all-dimension generic witness, and dimension-two exception. The full original canonical suffix beginning at Statement, including evidence, references and historical status check, is byte-identical to the archived published target.

The new presentation retains every quantifier and the original complex bilinear model, generic data, smooth-locus critical points, and n >= 3 scope. It correctly distinguishes the universal proof from the supplementary finite examples. The published conjecture and finite evidence retain the original authors' attribution.

The independent report, its checker, exact output and signed manifest remain byte-identical to the reviewed versions. The parent `RESULT.md` and `canonical-target.md` copies preserve their relative source bindings. Third-party source-page images remain private; the public package records their hashes and source/page locators. Removing these inspection-only images does not modify any signed artifact or required checker input.

## Complete visual and privacy inspection

I individually opened and inspected every final page: all seven solution pages and both canonical pages. The inspected PNG fingerprints are recorded in the unchanged packaging document record. Titles, author block, section headings, all displayed equations, numbered formulas, references, and page numbers are legible. I found no clipping, overlap, missing glyphs, unresolved references, or orphaned display introductions. The canonical renderer's three-line change inserts a page break only before RA-19's retained Statement and leaves other entries' rendering behavior unchanged.

Both PDFs have George Stepaniants's name and full Department of Computing and Mathematical Sciences, California Institute of Technology affiliation visibly in the content. The solution PDF metadata names George Stepaniants as author; the canonical PDF retains the collection's standard metadata. I extracted text and metadata from both final PDFs and found no contact email. The author block, canonical notice and resolution archive meet the authorized attribution request. The manuscript discloses substantial AI assistance and describes the independent audit accurately.

## Repository checks and completion record

The isolated branch is based on upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. The permanent registry is byte-identical, with all 217 mappings retained. The packager completed both required ID validations, the catalog update, all 17 ID safeguard tests and three status tests. I independently reran the three status tests successfully and checked the final source/target equivalence. The current final source checker and ID validators are recorded in the accompanying final verification JSON.

The original packaging [document record](document-checks.json), SHA-256 `9e6f4084c0cab176dd44ad973728ee46a0282873e9ab1e4490b095d2166d00bf`, is retained unchanged as a dated record of the handoff. Its statement that this coordinating conversion review was pending is superseded by this completed review. Its initial reference-file hashes describe that earlier snapshot, before this addendum and final publication evidence were added; the six canonical artifact hashes remain unchanged.

Current public eligibility is checked separately immediately before publication. This conversion review authorizes no mathematical scope extension. The submission remains subject to upstream maintainer review and merge.
