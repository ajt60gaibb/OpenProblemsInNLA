# MI-26 publication preparation — 2026-09-12

**PASS for handoff; the parent agent's independent final publication review is pending.** Preparer: OpenAI Codex agent `/root/formal_review_standards`. This report checks publication integrity and presentation. It is not an additional mathematical proof review, a human review, or a new Linux verification run. No commit, push or pull request was made by this preparer.

The immutable verified proof is revision `81176af27e570b59ba1e1a0745e28944e7d57c03`, [Linux run 34713045511](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34713045511). The two independent statement reviews and two independent final proof reviews remain unchanged. The independent [operational review](../linux-2026-09-12/OPERATIONAL-REVIEW.md) is SHA256 `9eae3acf9521e1dff4e9f4d8344ae3c7086687ed5655d973c8d939de4b9b09e0`; the complete original [evidence manifest](../linux-2026-09-12/EVIDENCE-MANIFEST.json) is `b06d99aa56964189dc9fbe1eea14dbfca2189b333f7cd43ee7f349fc033106fd`. These report seven successful Comparator exports and default-kernel replay with the documented isolation and rejection controls. They disclose that the adversarial nested bubblewrap attempt was denied at UID-map creation before its inner write.

## Preservation and exact scope

The new [integrity record](integrity.json), SHA256 `420e9502c5ebcf793075350f3b672cf6de17f3ecb24fa2ab303521c862ea39f0`, independently checks the following against the retained pre-edit record and actual Linux receipt:

- All nine mathematical source, numerical-target, Comparator and dependency-pin files are byte-identical to the verified revision. All four statement/proof referee reports are unchanged.
- Exactly 116 of the 118 verified input files remain byte-identical. The only changed verified inputs are the current project README and `formalization.yaml`; the artifact source snapshots preserve their historical versions.
- Every one of the 228 files bound by the Linux evidence manifest, plus the manifest itself, is unchanged: 229 retained files in total.
- The original canonical problem statement, references and historical status-check tail match both the verified revision and upstream `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`, after excluding only generated navigation and outer whitespace. The original informal Markdown, TeX and PDF are byte-identical.
- All other 216 canonical problem pages and all 217 permanent registry entries are unchanged. All 649 tracked files under the six previously verified problem directories and the shared Lean tools, workflow and documentation paths match the upstream base.
- The manifest's parsed data changes only `status.scope`, `review.status` and `review.notes`. All seven declarations, assumptions, formalization attribution and source attribution are unchanged. No email address was added.

The canonical page now records **Lean verified** on 2026-09-12, retains Matthew J. Colbrook's mathematical credit, and credits **George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA**, for the Lean formalization with AI-agent assistance. The existing RESOLVED entry includes the same formalization credit. The proof fully refutes the original complex PSD, real-valued concave-function assertion; it does not claim the optional positive-definite variant or refute a stronger hypothesis of globally nonnegative function values.

This publication branch is based on upstream `8b3d1157b73cd526bb4d0c2fd2dd1666d41812dc`. Its regenerated counts are **217 retained problems: 7 Lean verified, 82 Solved, 57 Open, 71 Partially resolved**. These are this branch's counts, not a count of other unmerged formalization PRs.

## Checks and rendered document

The [check record](checks.json) and raw logs record successful permanent-ID validation against both `origin/main` and `nla-upstream/main`, catalog generation, all 17 numbering tests, whole-catalog mathematical formatting checks, actual v0.4 manifest/Comparator coverage validation for all seven exports, and the final clean `git diff --check`. An initial whitespace diagnostic on the changed Markdown status line was fixed and its raw diagnostic retained; unrelated successful checks were not repeated.

The current repository renderer and GitHub-math filter produced a two-page A4 canonical PDF. Both rendered pages were visually inspected: the matrices, quadratic-form statement, seven declarations, credits, source links, command block and complete original problem are readable, with no clipping, missing glyphs or overcrowded page boundaries. The command block fits wholly on page 1. The render log contains no overfull-box or missing-character report. Temporary inspection images are `/tmp/nla-lean-formalization/mi26-publication/png/page-1.png` and `page-2.png`; their hashes are retained in the integrity record for the parent agent's separate visual review.

| Publication file | SHA256 |
| --- | --- |
| Canonical PDF | `9a0e129eb0ed28036371b6c39a8dd625a8bdd495a2c195b561587c1dd1c91632` |
| Canonical TeX | `57b1ed80c08cd864ae7f74d854eeadfdf9ee85812010db711a12ef3526ecac76` |
| Canonical README | `b0b24fc96ce9105d9e0428c886877ee412cf88f4ba10ea0c1e204f74540f9f8c` |
| Project README | `da52061298a2cfd339d4fcbceaf513c88e589ac7ebef37ce572c28e755f9bb6d` |
| formalization.yaml | `c444e408b373ee6a61e95c617fd72b05f100fe513811f764a8655759027e1230` |

Only the nine intended tracked publication files differ from the verified candidate, together with the newly retained Linux and publication evidence directories. The mathematical proof needs no alteration for this handoff. The parent agent should independently inspect this diff and both PDF pages before committing and opening the individual upstream PR.
