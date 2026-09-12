# SP-13 publication-conversion review

Reviewer: coordinating Codex agent `/root`, 12 September 2026 UTC.

**PASS.** I independently checked the complete publication conversion after the author's packaging work. This is separate from my [mathematical audit](SP-13-root-math-review.md) and the [independent full-proof review](SP-13-independent-review.md). It verifies preservation, presentation and attribution; it does not establish external human peer review or formal verification.

## Frozen publication artifacts

Paths in this table are relative to `eigenvalues-and-inverse-problems/SP-13/`.

| Artifact | SHA-256 |
| --- | --- |
| README.md | `c2f9ef4b951ced912886e32355d4e2dbd3e512dd6f821661ab7c671c98a49744` |
| solution.md | `0dc83e41e97ad5af6abe0b56dcb4ad588928c000eb59f71e9e0a038525486206` |
| solution.tex | `6045c4175a7723ca112a7b937797255f641480fefa55d21ce8d1414881ea15cd` |
| solution.pdf | `05c878660004d71860286468d5bc548b605a7533fa29646c460481b9fc412447` |
| problem.tex | `707d4274ec3814235e94e411c9699e6cfc1042fc4095c42d789e14ebe5c11840` |
| problem.pdf | `ee8ed73bbec000ea953607ce8d88344f8b83f0fb4f6613363e37b75e97352429` |

The final README cleanup removes only the two trailing spaces on the new Status line. Its parsed metadata and renderer body are unchanged, so it does not change the inspected TeX or PDFs. The mathematical source, original target and five other artifacts are unchanged.

## Independent source comparison

I directly extracted Sections 1-5 from the frozen candidate and canonical solution Markdown. Their 7,494 bytes are identical, SHA-256 `c89b2767c14af0419d403d8706bd446bad72ea4b76c28704b7290f67547d8dc0`; no mathematical wording normalization is needed. I independently compared their 121 ordered mathematical expressions with the generated TeX, ignoring whitespace only: all agree. I also compared the whole publication Markdown with the whole TeX: all 123 ordered mathematical expressions agree, including the two expressions outside the main proof. The distinction between these two counts is intentional.

The entire retained canonical suffix beginning at Statement is byte-identical to the original target, including assumptions, the unbounded-symbol and nonnormal scope, earlier partial results, references and dated search history. The permanent ID and canonical path remain unchanged. The historical ratings are retained and explicitly identified.

The published theorem still covers arbitrary complex E with trace norm o(n), arbitrary Hermitian H with the prescribed empirical spectral distribution, and every compactly supported continuous complex-plane test function. The essential published weak-type theorem is correctly identified by author, theorem number, page and normalization. Its original attribution is retained. No unproved strengthening, operator-norm bound or normality premise enters through the presentation.

I read both mathematical reviews in full. Their source hashes bind them to the unchanged frozen candidate. The independent reviewer reconstructed the proof and checked the primary external theorem separately. This conversion review does not substitute for that audit.

## All-page visual and privacy checks

I individually opened all five final solution pages and both canonical pages. I inspected the author block, theorem and quantifiers, the weak-type bound, the Hermitian transfer lemma, every finite-dimensional Schur estimate, the two limiting arguments, references and page numbering. All are legible, without clipping, overlap, missing glyphs, unresolved references, or orphaned display introductions. Normal paragraph continuation across a page boundary does not omit content.

George Stepaniants's name and full Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA affiliation are visible in the solution and canonical notice. Extracted PDF text and metadata contain no contact email. The solution metadata names George Stepaniants as author; the canonical document retains the collection's standard metadata. The resolution archive also includes the full authorized byline.

The renderer changes apply only to SP-13: plain solution page style, a separate reference page, and a canonical page break before the retained Statement in place of the earlier reference break. Other IDs' rendering branches are unaffected. The six reviewed output hashes above identify the exact artifacts; no rerender was needed for this review.

## Safeguards and remaining publication work

The package starts at upstream main `1f22006bdaa4659fcaa0bb775a887685cd3cc566`. The packager records both ID validations, the catalog update, 17 ID safeguard tests and three status tests as passing, with all 217 mappings preserved. Its standalone two-pass XeLaTeX builds and all-page visual inspection also passed. The final source checker, current public eligibility and actual upstream submission state are recorded separately at publication time.

I found no mathematical conversion or layout defect requiring an amendment. This review supports submission under the repository's independently audited Solved policy, with its actual informal AI review level disclosed. Upstream acceptance remains a maintainer action.
