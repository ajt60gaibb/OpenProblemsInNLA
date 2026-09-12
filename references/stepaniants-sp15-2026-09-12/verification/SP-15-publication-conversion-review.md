# SP-15 publication-conversion review

Reviewer: coordinating Codex agent `/root`, 12 September 2026 UTC.

**PASS.** I independently checked the complete frozen publication conversion after the packaging handoff. This review is separate from my [mathematical audit](SP-15-root-math-review.md) and the [independent full-proof review](independent-review-aa01/review.md). It checks preservation, presentation and attribution, not formal verification or external human peer review.

## Frozen canonical artifacts

The following filenames are relative to `eigenvalues-and-inverse-problems/SP-15/`.

| Artifact | SHA-256 |
| --- | --- |
| README.md | `6d617fc566cb9557210d6a4bd8b0613d7da5c014404739831dbe0ac4373e281a` |
| solution.md | `8bb2a7b37a34dfbd57544653e8ef8444a928a2de913e7ef017cd7312d5e95ebb` |
| solution.tex | `39ea64b3f28fc744ce62c8996c6aca6c095cb701aa376176b2a50196e2f41956` |
| solution.pdf | `9df7473dbdf3260d5ea50bbd8b1c2599a4057df3105e6fa90ef6583519cc4fbc` |
| problem.tex | `c62d995e99908134ac507337e9ab9c048c815c61c3e48f59cbb63ab15627270c` |
| problem.pdf | `01fd9df0cefe75c50ea1907d38817b3205dfc4e26e6c4b2db0eb8f8f7e3e0645` |

All six files remain byte-identical to the author's packaging handoff. No mathematical source or PDF amendment was required by this review.

## Source and exact-target preservation

I directly extracted the mathematical body from Exact target and conclusion through Section 4 in both the frozen candidate and the canonical solution Markdown. Their 7,308 bytes are identical, SHA-256 `b93675c67c4756099e5d0c169a02a789da304380e99fb0976a5b042b94a20722`. No layout or wording normalization is needed for this equality. All 116 ordered mathematical expressions in the proof agree with the standalone TeX after whitespace normalization. I separately compared all 20 mathematical expressions in the canonical README and canonical TeX; they also agree in order.

The complete original canonical suffix from Context and notation onward is byte-identical to the archived source, including the data definition, finite-bound quantifiers, earlier generic theorem, references and status history. The resolution precedes that retained record and labels the old ratings and search language as historical. No ID, path, assumption or target was reassigned.

I read the independent mathematical review in full. It separately reconstructed the noncommuting block determinant identity, the real nine-coefficient map, every possible full-matrix unitary intertwiner, and the positive-dimensional constant-rank fiber. Its signed report and exact source binding remain unchanged. The presentation preserves the distinction between unitary similarity and ordinary similarity and between one exceptional infinite fiber and the established generic-finiteness theorem. It claims neither a smallest counterexample dimension nor a numerical specification of the fiber.

The original question and generic theorem retain Fortier Bourque and Ransford's attribution. The standard constant-rank theorem is identified as the general external result used. The signed independent checker is a supplementary universal polynomial diagnostic; it is not described as a formal proof of the differential-topological argument.

## Complete visual and privacy inspection

I individually opened every final page: all four solution pages and both canonical pages. I inspected the author block, full theorem, block matrices and Schur complements, coefficient count, gauge restrictions, constant-rank proof, references, headers and page numbers. All content is legible, with no clipping, overlap, missing glyphs, unresolved references or orphaned display introductions. The page adjustments keep the displayed Schur calculation and parameter pair together without changing the source mathematics.

George Stepaniants's name, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA are visible in the manuscript and canonical notice. I confirmed the full byline with normalized `pdftotext` extraction and inspected PDF text and metadata for contact email; none is present. The solution metadata names George Stepaniants as author, while the canonical PDF uses the collection's standard metadata. Substantial AI assistance and the actual informal audit level are disclosed. No third-party full paper or inspection-page image is included in the public package.

The renderer modifications are restricted to SP-15 display/section keep-together instructions and the canonical page break before the retained context. The existing IE-05 behavior is preserved when that condition is shared. No other problem's mathematical content or rendering branch is changed.

## Repository and publication gates

The package starts at upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. Both ID validators, all 17 ID tests, three status tests, catalog generation and the packager's source checker passed. All 217 permanent registry mappings remain unchanged. The source checker confirms the exact mathematical body, original target, signed reviews and formula sequences. The two standalone documents compiled twice with XeLaTeX and passed the packager's separate visual inspection before this coordinating inspection.

Current public eligibility and final verification are recorded separately immediately before publication. The independent mathematical PASS, coordinating mathematical PASS and this complete conversion PASS support submission under the repository's Solved policy. Upstream review and merge remain maintainer actions.
