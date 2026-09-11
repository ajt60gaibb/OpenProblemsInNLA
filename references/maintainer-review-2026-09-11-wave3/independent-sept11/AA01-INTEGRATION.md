# AA-01 integration preservation audit — 11 September 2026

**Verdict:** The separately submitted, independently reviewed AA-01 manuscripts can coexist without changing the target, permanent ID or mathematical status. Integration must combine the canonical resolution notices and regenerate the canonical TeX/PDF; choosing either side wholesale would discard attribution and evidence from the other submission. This is a preservation audit, not a new proof review or a determination of independent derivation, novelty or priority.

## Exact revisions and checks

Read-only Git inspection in `/private/tmp/nla-review-wave2-20260911` compared published `origin/main` at `87366c62d3b5c47d170f747b1cb40ab38d501013` (including PR #89, reviewed at `3443179cb62b410678f3c67f26cd8df56ba6133a`) with PR #68 at `2a1a0b39992bbd5654e7bdf9f869e21a6cee0d71`. Their merge base is `16369809e6e600144bd350ab70b7473b652f46f1`. No fetch, checkout mutation, merge, publication, checksum computation or test rerun was performed.

The complete text between `## Problem statement` and `## References and status` is exactly equal in the base, published main and PR #68. This preserves finite constant-free computation trees, independent operation errors, exact comparisons and negation, branching and stored reuse, all real inputs, exactness at zeros, and the complete accuracy/decidability quantifiers. The references and historical audit text also agree; only the dated historical heading differs (`Status check` versus `Earlier status check`). Difficulty, importance and their historical rationale agree.

All three parsed `problem_ids.json` mappings are exactly equal, with 203 entries and `AA-01` mapped to `arithmetic-and-complexity/AA-01/README.md`. There is no ID or path conflict and no basis for assigning a second ID to the second manuscript.

## Conflicts and recommended resolution

| Path | Actual overlap | Required preservation |
| --- | --- | --- |
| `arithmetic-and-complexity/AA-01/README.md` | Both branches insert a resolution notice immediately before the unchanged original statement. Published main lines 13–22 contain Colbrook's notice; PR #68 lines 13–19 contain Stepaniants's notice. | Keep **Status: Solved** and 2026-09-11, retain both author-specific notices with their distinct theorem locators, manuscripts and review links. A shared introductory sentence can say that two separately submitted manuscripts received independent agent review. Do not imply joint authorship, independent invention or priority. |
| `arithmetic-and-complexity/AA-01/problem.tex` | Both regenerate the same canonical document with only their respective resolution notice. | Regenerate from the combined README; neither side alone represents the integrated page. |
| `arithmetic-and-complexity/AA-01/problem.pdf` | Both replace the same generated binary. | Rebuild from the combined document and inspect the resulting pages. Selecting either old PDF would omit one submission's notice. |
| `arithmetic-and-complexity/AA-01/solution.md`, `solution.tex`, `solution.pdf` | Added only by PR #68; no published #89 file at these paths. | Retain as Stepaniants's separate complete manuscript and landing page. `solution.md` lines 3, 8 and 10 explicitly identify the author, theorem locators and review. Do not replace these with Colbrook's manuscript. |
| `references/stepaniants-2026-09-11/` | New separate provenance subtree from PR #68. | Retain the submission record, original AA-01 user source and `verification/reviews/AA-01-review.md`. Preserve the distinct Guo–Fang–Lu attribution in the unrelated MD-03/MD-04 material as already corrected. |
| `references/colbrook-arithmetic-2026-09-11/` | Existing separate #89 proof/provenance subtree; absent in PR #68 only because that branch predates #89. | Retain the whole published subtree, including complete AA-01 TeX/PDF, supplied source, both AA-01 reviews, experimental-evidence limitations and unrelated partial AC-11/AC-12 evidence. A two-tip diff reporting these files as deleted is not a PR #68 deletion; neither branch deleted the other's additions from the common base. |
| `RESOLVED.md` | Published main lines 359–363 describe Colbrook's AA-01 resolution; PR #68 lines 18–26 add a three-target submission section with a separate Stepaniants AA-01 paragraph. | Preserve both attributed records, preferably cross-link them or present both under one AA-01 target heading. AA-01 remains one solved catalog target. Distinguish the two source packages and keep both manuscripts/reviews discoverable. |
| `CATALOG.md`, category/root summaries | Both branches contain generated counts reflecting different surrounding resolutions. | Regenerate from combined canonical statuses. The second AA-01 manuscript does not cause another decrement in the open count. |
| `problem_ids.json` | No conflict; all 203 mappings equal. | Retain the published registry unchanged. |

## Evidence and provenance that must remain visible

* **George Stepaniants:** `solution.tex` / `solution.pdf`, Theorem 2.1 and Corollary 7.1; `references/stepaniants-2026-09-11/verification/reviews/AA-01-review.md`; source record at that subtree's README, especially lines 13, 17 and 21–31. The signed-order gap characterization and real-quantifier elimination settle the exact tree model, with no efficient running-time claim. The ChatGPT provenance and distinction between agent review and human/formal review remain intact.
* **Matthew J. Colbrook:** `references/colbrook-arithmetic-2026-09-11/manuscripts/AA-01.tex` / `.pdf`, Theorem 1.1 and Sections 2–4; both `AA-01-review.md` and `AA-01-second-review.md`; subtree README lines 7, 11–17. Its independently reviewed mathematical proof supports Solved, but the missing experimental programs, reported counts, compiler/solver claims and logs remain outside that certification. The exported manuscript's dated verification notice at TeX line 39 explains that original pending-review language is historical.
* Preserve the September 10 literature check as **Earlier status check**, avoiding the implication that its old “open” wording supersedes the September 11 resolution. The historical references and exact original target should not be removed or rewritten.
* Stepaniants's record of its earlier public-branch search is explicitly dated and limited to the then-accessible branches. Retain that as submission history; it must not become a present-tense claim that no other AA-01 resolution exists after #89. A short integration note acknowledging both current submissions is sufficient without altering the original record.

## Integration observation

At the last inspection, local integration branch `codex/review-wave2` had advanced to `66bb1c6b827029ab52db4a92b749d34663ac87ba` (merge of #85), and still contained only the published Colbrook AA-01 notice. No merged #68 result was yet available for a post-integration preservation check. The recommendations above describe the concrete required resolution; they do not claim that integration is already complete.


## Final integrated preservation check — PASS

Checked immutable integration commit **`d65e757a425d0cf709ac4969399b37cbce7b684c`**, titled “Merge pull request #68 preserving both AA-01 proofs and original IDs”. The scoped working files were clean and matched this committed state. This supersedes the pending observation above.

The combined canonical `arithmetic-and-complexity/AA-01/README.md` retains the complete Colbrook notice from reviewed #89 at lines 13–22 and the complete Stepaniants notice from reviewed #68 at lines 24–32. Both original notices are present verbatim inside their respective blocks. Both authors and affiliations, distinct theorem locators, manuscript links, all three proof reviews, source records, AI provenance, agent-versus-human/formal-review qualifications and historical ratings remain present. Colbrook's missing experimental programs and uncertified run-count/compiler/solver claims remain explicit at line 20; Stepaniants's no-running-time-bound qualification remains at line 29. No notice merges authorship or asserts priority.

The full original target body at lines 34–67 is exactly equal to the published base, pre-integration main, and both reviewed PR heads. All 203 permanent-ID mappings are exactly equal. The historical literature audit now has the unambiguous “Earlier status check” heading at line 88.

Direct source-content comparisons, without checksums, confirm that the separate manuscripts, source records and proof reviews are unchanged from their exact reviewed PR heads: Stepaniants's `solution.md/.tex/.pdf`, original AA-01 user source, review and package README; Colbrook's exported AA-01 TeX/PDF, supplied original TeX, both reviews and package README. Every relative link in the combined canonical introduction resolves to a committed file. `RESOLVED.md` retains separately attributed entries for both manuscripts, and the generated canonical `problem.tex` contains both authors. PDF visual inspection remains with the integration owner as requested.

**Final verdict: PASS — both reviewed AA-01 submissions, their limitations, the exact original target and the permanent IDs are safely preserved. No remaining content-preservation blocker.**
