# IE-19 independent operational review — 2026-09-12

**Verdict: PASS for the actual remote Linux verification run and its correspondence to the previously reviewed IE-19 proof.** Run [34703188616](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703188616), attempt 1, completed successfully on GitHub-hosted Ubuntu 24.04 at **531941ca0062049ccf03d3f2df418ea805ac4036**. This review supports promotion of the exact original IE-19 target to `Lean verified`. It does not certify the manuscript's separate all-parameter sharp replacement.

Reviewer: Codex agent `solved_statement_inventory`, independent of the IE-19 proof author. This agent previously completed `reviews/proof-referee-1.md`; that review's SHA256 is `c168b3b4eb71cdd33cdb7aec2ac15bbbacfdbc14b479c706d317106632875cea`. The review applied the Tau Ceti correctness, scope, proof quality, reuse and attribution criteria; it was not a run of the Tau Ceti service or external human peer review.

## What was independently checked

I fetched fresh run, job and artifact metadata through GitHub CLI and downloaded both original artifact ZIPs and the full workflow-log ZIP. I checked ZIP integrity, byte lengths and published SHA256 digests; all 23 extracted artifact members match the coordinator's earlier downloads. I read the actual verification, control and bootstrap logs and the exact committed workflow/harness, and recomputed source hashes against Git objects at the verified commit. The audit did **not** rerun Comparator on this macOS machine, launch a second Linux run, or independently rebuild the recorded Linux binaries. The execution evidence comes from GitHub Actions; the download, source-comparison and log review checks were performed locally.

All three jobs (`select`, `checker-controls`, and `verify (IE-19, linear-systems-and-elimination/IE-19/lean)`) and every recorded step succeeded. The run was triggered by a push and ran from 15:45:34 to 15:53:46 UTC. The verification job's checkout log prints the exact commit above.

| Original artifact | ID | Bytes | SHA256, matching GitHub API and upload log |
|---|---:|---:|---|
| `lean-IE-19` | 10301556043 | 15131 | `6bae8ff486ad17d2f68c887eda7e7ee6b9e4ea42b0a4faf000b987a398fe28e6` |
| `lean-checker-controls` | 10301231188 | 8102 | `7f18efd9c02565adfd3589bc686db99a5438ee1916323264b8ba87a4eac9c313` |

All **29 project inputs** in the successful `result.json` match the exact committed Git objects. The five mathematical files (definitions, challenge, numerical targets, proof and exports) also match the frozen hashes in the prior independent proof review. Their full hashes and those of all review reports are retained in [source-integrity.json](independent-audit/source-integrity.json). In particular:

- `Proof.lean`: `06a534c417911f7db8aca8310699c3862eaf535f8b34ec20b5551218c20a5460`.
- `Solution.lean`: `72fa6092d37c32eb453af0ba83974cc541cb15730080c96dfbaa9226a6f6f658`.
- `comparator.log`: `a5d84db15a2f28c685a954db37f32c55736a8c1db0297674357a43fbb3c35d4d`.
- successful `result.json`: `757ffc0d3446ab8f9ffa0d289845b7947bd14c222178004c7709f6a71e159a95`.

## Checker, dependencies and controls

The tool receipt binds Lean **4.33.1** (Linux x86_64), the Forsythe tool-source revision `8d1b0c0545a77b40245e84705aa7d273e6c81e62`, and source-lock SHA256 `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b`. I independently hashed all **58 locked source files** and reproduced the CI probe transformation: its SHA256 `31057195baf238807cacbb4126c5b07f02cec55a4e4437de5f3a755b3fada803` matches the receipt. The actual tool-build logs succeeded, and the control and project runs have identical tool receipts, including executable hashes. The committed harness checks those hashes before verification. This is source/receipt consistency evidence, not an independent reproducible build of each Linux executable.

The harness snapshots ordinary tracked files from the commit into a new temporary project, excluding compiled project artifacts, checks input immutability, and logs fresh source clones/checkouts for all **10 manifest dependencies**. These include LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926` and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. It then uses the official Mathlib compiled cache (8690 files) before fresh project and LeanCert elaboration. This was not a rebuild of every Mathlib module from source.

Both the separate checker job and the project verification executed the real sandbox and checker controls. The logs establish successful build/export isolation probes, private namespaces and blocked network/process/write escape probes; an honest kernel replay passed while an invalid raw proof and a quotient-postcheck mismatch were rejected. Five Comparator fixture runs returned their expected outcomes, including statement/kind mismatch and illegal-helper-axiom rejection. `simple_kind_mismatch` duplicates the helper-axiom fixture, so these are not five distinct rejection categories. Additional fixtures rejected `sorryAx` and the actual Lean 4.33.1 native-execution axiom `checked._native.native_decide.ax_1_1`. Expected negative exits were 1; the phase checks and control harness exited 0. The CI sandbox adaptation uses pipes, deadlines and a probe-only permission to execute the nested-namespace attack; it preserves the isolation assertions and does not substitute a fake sandbox.

The actual Comparator run separately built and exported `Challenge` and `Solution`, with no permitted definition holes. It matched these three declarations and their statement dependencies:

- `NLA.IE19.counterexample`
- `NLA.IE19.not_lowerBoundConjecture`
- `NLA.IE19.not_sharpConjecture`

The allowed and printed axiom dependencies are exactly `propext`, `Classical.choice` and `Quot.sound`. The three deliberate `sorry` warnings occurred only in the challenge template. The successful solution passed transitive axiom checking, Lean's **default kernel replay in a fresh environment**, and the quotient consistency postcheck. The log ends with `Lean default kernel accepts the solution`, `Your solution is okay!`, and `EXIT_STATUS=0`. This is not a claim that a second independently implemented kernel was used. Comparator's result correctly says `semantic_review: not-performed-by-this-command`; the earlier independent statement/proof reviews supply that separate correspondence assessment.

## Publication handoff and evidence

The verified scope is the exact admissible 3-by-3 counterexample, true inverse and induced infinity norm, yielding `7/9 < 5/4` and negating the full original lower-bound and sharp conjectures. The mathematical source remains attributed to Matthew J. Colbrook; the Lean formalization is attributed to George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. No email address is included.

Evidence is retained under [independent-audit](independent-audit/): the original ZIPs, fresh API metadata, complete workflow logs, exact locked tool/harness sources, and machine-readable artifact/source/dependency/control integrity checks. [evidence-manifest.json](independent-audit/evidence-manifest.json) records SHA256 and byte lengths for every retained evidence file. The two original GitHub artifacts are scheduled to expire on **2026-12-11**; retain their original ZIPs and this review in the publication evidence archive so verification remains reviewable after expiration. Neither this report nor its proposed promotion text has been committed, pushed, or represented as already present at the verified revision.
