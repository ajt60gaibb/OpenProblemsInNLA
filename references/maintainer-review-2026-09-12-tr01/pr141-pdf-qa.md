# PR 141: TR-01 target, source, links, and PDF audit

Reviewed frozen PR head `2c7655f234bbb3b3134133ebae34eb479e9469e1` against main snapshot `41f602301ca99f4e1e92d0e61f44fc4f6d101604`. The public proof revision is `ed21181197ac839eac95f549404f94e7e3aa6e10` in `yuningyang19/OpenProblemsInNLA_TR-01`. Review date: 2026-09-12.

**Corrected artifact verdict: PASS for target, source, and PDF packaging**, subject to the independent Lean auditor's result and the parent's inclusion of its pending report. The exact corrected file hashes below bind this verdict. Original target preservation, stated theorem correspondence, PDF legibility, ordered Markdown/TeX formulas, and immutable proof link bindings pass.

**Frozen-head verdict: publication repairs required.** Two basis-matrix transcription errors, removal of historical status notes, and a misleading cold-build evidence link required correction. The parent repaired them and rebuilt the canonical PDF; the frozen evidence and findings remain separately recorded below.

This is read-only packaging and theorem-boundary review. Independent review of the complete manuscript and fresh Lean verification belongs to the other assigned auditors. The phrase “Lean verified” is not independently certified by this report.

## Findings and exact recommended repairs

1. **P2: subspace used as a matrix.** At frozen `randomized-and-low-rank-approximation/TR-01/README.md:39`, `V` denotes an r-dimensional subspace, but line 48 uses `V^T Omega Omega^T V`. The same mismatch occurs in `RESOLVED.md:38` and line 41. Define an orthonormal basis matrix `U in R^{n x r}` with `U^T U = I_r` and `range(U)=V`, then use `U^T Omega Omega^T U-I_r` in both probability formulas. An arbitrary basis is insufficient. Preserve the one universal constant, the exact prescribed width, and the fixed-subspace quantifier outside the probability. The pinned manuscript itself already defines its `V` as an orthonormal matrix, so this is a catalog transcription defect. The parent's current Markdown defines `U` correctly in both locations.

   Suitable prose is: “There is a universal C >= 1 such that, for every power-of-two n, every 1 <= r <= n, every 0 < epsilon < 1, and every fixed r-dimensional subspace V, choose an orthonormal basis matrix U in R^{n x r} for V. With k=min{n,ceil(Cr/epsilon^2)}, the failure probability Pr{||U^T Omega Omega^T U-I_r||_2 > epsilon} is at most 0.01.” The equivalent RESOLVED event has norm at most epsilon and probability at least 0.99.

2. **P2: historical audit paragraphs removed.** The replacement starting at frozen canonical README line 37 deletes the earlier “Status check” and “Audit — 2026-09-10” paragraphs. Retain their exact text under historical headings following the current resolution/evidence. Recoverable source: `pr141-source/base-README.md`. Their old unsuccessful searches describe historical evidence and must not be presented as the current unresolved status. The parent's current Markdown restores both paragraphs, with “Historical status check — 2026-09-10” and the dated audit heading.

3. **P2: cold rebuild link does not itself record success.** Frozen canonical README lines 85 and 90 describe successful cold rebuilding but link only `lean/audit/cold_rebuild.json`. That immutable record has build return code 1 and `sources_unchanged: false`. `lean/audit/cold_recovery.json` records return code 0 after a repair to the boundary-check client; it reports `mathematical_sources_changed: false`, no reused development project cache, and reused dependency cache. Link both, labeling the former as the retained failed initial attempt and the latter as successful recovery. Suggested prose: “The archived cold project rebuild first failed in the boundary-check client; the separate recovery record reports success after that client was repaired, with mathematical proof sources unchanged.” This finding was flagged by the Lean auditor and independently confirmed by reading both JSON records. Parent reports the canonical Markdown has now been corrected.

4. **Source disclosure requires accurate treatment; corrected.** The manuscript auditor identified outdated disclosure in the pinned manuscript PDF while its TeX disclosure is newer. This packaging reviewer verified the PDF theorem boundary on page 2, not every page of the external manuscript. The separate `pr141-manuscript-pdf-qa.md` report isolates the difference to an added abstract sentence and changed acknowledgments, with mathematical source unchanged; I read that report. The corrected canonical page explicitly records the stale acknowledgment and points to the artifact review. No claim that the entire external manuscript PDF and TeX are identical is made here.

Author attribution in the parent's correction names Yuning Yang, School of Mathematics, Guangxi University, as printed in the immutable manuscript. This transcribes source attribution and does not assert independent identity verification.

## Original target and theorem correspondence

The complete canonical problem statement is byte-identical to the main snapshot. The original reference paragraph and the append-only registry are also retained; the registry is byte-identical to main. Canonical path remains `randomized-and-low-rank-approximation/TR-01/README.md`.

The pinned manuscript's Theorem 1 is on page 2, as linked. It uses a power-of-two ambient dimension, a deterministic orthonormal n-by-r frame, two independent Rademacher diagonals, two normalized Walsh transforms, and a uniformly sampled k-coordinate subset without replacement. Its normalization is sqrt(n/k). It supplies one universal constant and the exact width `min{n,ceil(Cr/epsilon^2)}`, including the full-width cap, with failure probability at most 0.01. Its range `0 < epsilon < 1` contains the canonical `0 < epsilon < 1/2` range. The supremum over frames is outside the probability; it does not claim one random draw works simultaneously for all subspaces. The matrix event is equivalent to the stated norm bounds for every vector in the fixed subspace. Thus there is no target substitution, altered sampling law, weaker-width substitution, or dimension mismatch after the basis notation repair. This checks the source statement, not its full proof.

The original workshop Definition 5.3 and Problem 5.6 have the same two-round law and ask for order r/epsilon^2 width. TR-01 prescribes the explicit capped width, and the manuscript states that formulation directly. See the primary [workshop source](https://arxiv.org/html/2602.05394v3) and the [immutable manuscript](https://github.com/yuningyang19/OpenProblemsInNLA_TR-01/blob/ed21181197ac839eac95f549404f94e7e3aa6e10/manuscript.pdf).

## PDF and link checks

Both frozen canonical PDF pages were rendered with Poppler to scratch PNGs and inspected in full. Formulas, fractions, superscripts, dimensions, probability thresholds, source names, and list entries are legible, with no overlap or clipping. Text extraction found zero out-of-bounds characters and zero replacement characters. The paragraph crossing from page 1 to page 2 has normal continuation. All 26 Markdown math expressions match the TeX expressions in order, ignoring whitespace only; this includes the frozen notation defect above.

All 25 checked link occurrences resolve structurally: 16 immutable public proof occurrences (15 distinct links), and 9 local paths. The public links all bind to `ed21181197ac839eac95f549404f94e7e3aa6e10`; each linked path exists in the exact clean public clone at `/private/tmp/nla-tr01-proof`. This is commit/path validation, not an HTTP request to each URL. The proof revision was checked with Git. The pinned toolchain is `leanprover/lean4:v4.33.0`, and the mathlib revision is `db584cd6d46c92f209a44c0f1c829460d327499d`, matching the displayed pins.

## Frozen artifact hashes

| Artifact | SHA-256 |
| --- | --- |
| README.md | `ce0bb47c31a6e4aaa6f2afddac0376ff4de4403130dce3b2756b22761f463ff8` |
| problem.tex | `b11c595826befcf367acdc0ef03141651f2835e86b6cb45a1e59cb27ff75a5ec` |
| problem.pdf | `51591709e8d3749cb3ac4df5994195fd491efc66b70763ead2e23140f7a82321` |

Evidence: `/private/tmp/nla-review-inequalities/pr141-source/` and `/private/tmp/nla-review-inequalities/pr141-pdf-qa/checks.json`, with both canonical page renders, extracted text, and the inspected manuscript theorem page in the latter directory. No authoritative files were rendered, edited, or recompiled by this auditor; only scratch PNGs and reports were written.

## Corrected artifact addendum

Reviewed the parent's uncommitted repairs on branch head `2c7655f234bbb3b3134133ebae34eb479e9469e1`; the hashes below, rather than the unchanged branch HEAD alone, identify the corrected snapshot. All three corrected canonical PDF pages were rendered to scratch and inspected in full. There is no clipping, overlap, broken glyph, or illegible expression. The axiom list continues onto page 3; its continuation is clear. All 28 Markdown math expressions match TeX in order, ignoring whitespace only. Extracted PDF text has zero replacement characters and zero out-of-bounds characters.

The original problem and references blocks remain byte-identical to the reviewed main snapshot. Both historical audit paragraphs are retained. The basis matrix is now explicitly orthonormal and appears consistently as `U` in the canonical and RESOLVED Gram expressions. Author attribution is present. The cold-build failure and successful recovery now have separate accurately labeled immutable links. The external PDF disclosure caveat is present and legible. The new catalog-review paragraph clearly attributes the informal reviews to Codex agents and defers exact executed Lean checks to the dedicated audit.

Of 35 corrected link occurrences, all 17 immutable public proof links bind to existing paths in the exact pinned commit. The local manuscript PDF review is now present. The sole missing local target at review time is `references/maintainer-review-2026-09-12-tr01/pr141-lean-review.md`, which the parent explicitly identified as a pending report to include before publication; it is not classified as an unintended broken link. Publication with “Lean verified” remains contingent on the separate formal audit and that report's inclusion.

| Corrected artifact | SHA-256 |
| --- | --- |
| README.md | `8ba2a5fbf9935787b5171a5945715bc795e6f50b3cd1783661448cb24c464122` |
| problem.tex | `10ae690b9ee4bd31c6d2cc46095cea203ef0a3c76d9f5dc80c329855ba7c5555` |
| problem.pdf | `646231648d987ebb85c82ec2ddd61853b461a8749da481ad8688edc16a2c959b` |
| RESOLVED.md | `3a6bdf2b1ec8c6413ef247f0d9df8cbc3232f53e81e8df26bb9b09a606c3f5c8` |

Corrected snapshot, three renders, text, and `checks.json` are in `/private/tmp/nla-review-inequalities/pr141-corrected/`. Checker: `/private/tmp/nla-review-inequalities/check_pr141_corrected.py`. Only scratch files were written. Any later canonical text or PDF modification requires updating this artifact binding. The formal auditor has separately flagged a possible missing prerequisite build for the optional graph command; that reproduction issue belongs to its verification findings and may require a further documentation update.
