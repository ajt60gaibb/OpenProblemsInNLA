# RA-03 Linux verification: independent operational review

**Verdict: PASS, 12 September 2026.** The actual [GitHub Actions run 34704564047](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34704564047) checked proof commit `973f95969701601dcae7b30683b175843baa9c22`. All three jobs and every recorded step succeeded. The project verification step ran from 16:14:17 to 16:22:33 UTC; it was not skipped.

This is an independent audit of execution and evidence by agent `formal_review_standards`. Mathematical fidelity is covered separately by the two frozen proof-referee reports retained in `source/`. This reviewer did not author RA-03's proof or statements. The reviewer helped implement the shared harness and therefore does not present this operational audit as an independent source-code review of that harness; its separate source review and previous Linux audit are recorded with the infrastructure.

## Identity and preserved evidence

The project is `randomized-and-low-rank-approximation/RA-03/lean`. All **48** project inputs in the result receipt are exactly the complete Git-tracked input set at the checked commit, with byte-for-byte agreement between receipt hashes, immutable Git blobs and the reviewed worktree. The five frozen mathematical files agree with both prior proof-referee hash tables. `comparator.json`, all ten dependency revisions, the toolchain and tool source lock agree with that commit. The harness, workflow and CI toolchain have no changes from the successfully audited infrastructure commit `214c142d6bfe0f0c338808f188062acbbad0fb19`.

Both original ZIPs were downloaded, checked against GitHub's published SHA-256 digests, safely extracted, and compared with every extracted file:

| Artifact | ID | SHA-256 |
|---|---|---|
| `lean-RA-03.zip` | 10300997836 | `3c26241f0fb27beae769efae5bcc09493a4a25378a8729164563e813146b0b0e` |
| `lean-checker-controls.zip` | 10301207078 | `b9f0fe273995ce7c2b0802aceb106d8afbce73a4225a1654cf4cda6a86d1156c` |

Raw run/job/artifact metadata, the full run log, both ZIPs and all 23 artifact files are retained here. `identity-verification.json`, `control-verification.json` and `audit_checks.py` record the additional review checks. The evidence manifest binds this report and the retained files.

## What actually ran

The standalone checker job and the RA-03 job each executed the real Linux controls. Both sandbox modes ran as UID 1001 with six private namespaces, no effective capabilities and `no_new_privs`. Network/AF_UNIX access and writes, truncations, symlink writes and creation outside the allowed build directory were denied. Build-directory writes were allowed only in build mode; export remained read-only. All four unsupported sandbox option probes failed closed. The nested `bwrap` executable ran and was denied UID-map setup before its inner write; this does not claim that the inner write was reached.

Both jobs exercised all three raw-kernel replay controls: an honest proof with inductives and quotients was accepted, an invalid raw proof was rejected, and a forged quotient declaration was rejected by the quotient post-check. All five full Comparator fixtures reached both build and export phases and returned the required outcomes. The two additional full Comparator negative controls rejected `sorryAx` and the actual generated native-evaluation axiom `checked._native.native_decide.ax_1_1`.

RA-03 was copied into a fresh verification directory and all ten pinned dependency repositories were cloned there. The run used the 8,690-file Mathlib cache; it did **not** rebuild every dependency from source. Its own Definitions, Challenge, Proof and Solution were freshly elaborated. Challenge completed its 2,723-job graph with four intentional statement placeholders; Solution completed its 3,731-job graph with no warnings. Twelve axiom reports, including all four exports, contained exactly `propext`, `Classical.choice` and `Quot.sound`.

The actual Comparator built and exported both modules for:

- `NLA.RA03.frobeniusSq_eq_norm_sq`
- `NLA.RA03.process_isProbability`
- `NLA.RA03.counterexample`
- `NLA.RA03.not_squaredErrorConjecture`

It then printed `Lean default kernel accepts the solution` and `Your solution is okay!`, exiting zero. The receipt is `comparator-accepted`, using Lean 4.33.1 and the pinned, hash-checked Forsythe Comparator/exporter adaptation with the strict sandbox. No extra axiom is permitted.

## Scope

The audited exports include the actual Frobenius norm bridge, normalization of the sequential conditional pivot process, the exact one-step counterexample and the negation of the original universal squared-error conjecture. The earlier mathematical referees checked these meanings against the original statement and Colbrook's solution; the Comparator checks the frozen formal declarations and proof dependencies, not equivalence to English prose. The source's optional sharp-rank family and Cholesky discussion are outside this formalization. The evidence supports publication of these four verified exports; no operational blocker was found. This review itself changes no repository status.
