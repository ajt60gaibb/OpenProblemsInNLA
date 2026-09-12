# MI-29 Linux verification: independent operational review

**Verdict: PASS, 12 September 2026.** [GitHub Actions run 34706412510](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34706412510) succeeded at immutable proof commit `c0c5eced77d2528f37d931200248fc54a190813e`. All three jobs and every recorded step succeeded. The actual project verification step ran from 16:50:50 to 16:57:17 UTC; it was not skipped.

Reviewer: OpenAI Codex agent `/root/formal_review_standards`, independent of the MI-29 proof implementer. This agent previously served as statement and final mathematical referee 2. It also helped implement the shared harness, so this operational audit is not presented as an independent source-code review of that harness. The separate infrastructure review and the other mathematical referee remain distinct records.

## Exact identity and original artifacts

All **70** inputs in the project receipt form exactly the complete Git-tracked project input set at the checked commit. Every receipt hash matches both its immutable Git blob and the pre-publication working file. The five frozen mathematical files match both final proof-referee hash tables. The configuration selects exactly five public declarations, no replaceable definition holes, and only `propext`, `Classical.choice` and `Quot.sound`.

Both original artifact ZIPs were downloaded, checked against GitHub's SHA-256 digests, safely extracted, and compared with every extracted file:

| Artifact | GitHub ID | SHA-256 |
|---|---|---|
| `lean-MI-29.zip` | 10302520086 | `6e7bee31f8a63c95b448e0ca6391b3e3e88e25cba43c03a211f5c9ebbb6b0947` |
| `lean-checker-controls.zip` | 10302140601 | `e5ba51f3885e8dd64d3dbf762cdcf5dda4b969d654911c7d7ae4a5b854284479` |

This directory retains raw run/job/artifact metadata, the full run log, both original ZIPs and all 23 extracted artifact files. `identity-verification.json`, `control-verification.json` and `audit_checks.py` record the additional checks; the evidence manifest binds the retained bytes. The preliminary source record is explicitly historical and is superseded by this final operational verdict.

The complete shared tooling and workflow match upstream `02b807770fca860ef810cc048d6849224b8f93e1`. The actual harness, source lock and bootstrap/selftest/verify wrappers are unchanged from successfully audited infrastructure revision `214c142d6bfe0f0c338808f188062acbbad0fb19`. Comparator/exporter, Landrun and the derived probe remain bound by the same source lock. The newer upstream selector and documentation preserve the real checker and standard-axiom policy.

## Actual controls and proof verification

Both the standalone checker job and the MI-29 job executed the real Linux control set. Build and export modes ran as unprivileged UID 1001 with six private namespaces, no effective capabilities and `no_new_privs`. Network and AF_UNIX access, outside writes, truncation, symlink writes and creation were denied. Build-directory writes were allowed only in build mode; export remained read-only. Four unsupported sandbox option probes failed closed. The nested `bwrap` executable was invoked and denied UID-map setup before the inner write; that inner write was not reached. As the maintainer's documentation states, read-only host mounts provide no general host-file confidentiality; this run used the isolated GitHub Actions runner.

In each job, all three actual raw-kernel replay probes behaved correctly: the honest inductive/quotient fixture passed, the invalid raw proof failed, and the forged quotient declaration failed the quotient post-check. All five full Comparator controls reached both build and export phases and returned the expected results. Additional full Comparator controls rejected `sorryAx` and the generated native-evaluation axiom `checked._native.native_decide.ax_1_1`. Nothing was replaced by a simulated sandbox or inferred from a mere build success.

All ten dependency repositories were freshly cloned and checked out at the pinned revisions. The matching Mathlib cache supplied **8,690** files; this was not a complete dependency rebuild. The project's own Definitions, Challenge, Proof and Solution were freshly elaborated. Challenge completed its **2,710-job** graph with the five deliberate interface placeholders. Solution completed its **3,147-job** graph with no warnings. Fifteen internal/public axiom reports contained exactly the three standard axioms.

The actual Comparator built and exported both environments for:

- `NLA.MI29.spectralPower_natCast`
- `NLA.MI29.modulus_power_eight`
- `NLA.MI29.comparison_positive_real`
- `NLA.MI29.counterexample`
- `NLA.MI29.not_modulusDeterminantConjecture`

It then printed `Lean default kernel accepts the solution` and `Your solution is okay!`, exiting zero. The receipt records `comparator-accepted` under Lean 4.33.1. The scalar certificate remains explicit kernel-mode LeanCert and has no native-execution axiom in its transitive dependency closure.

## Scope and conclusion

The exports include the genuine CFC/natural-power and square-root-modulus bridges, positive-real determinant interpretation, the full admissible rational witness, and the negation of the original all-dimension, all-matrix, all-nonnegative-real-exponent conjecture. The already-retained mathematical reviews checked the English-to-Lean correspondence. Comparator checks formal identity and kernel trust, not equivalence to English prose. The separate singular-input extension, established `k=2` theorem and positive-`B` variants are outside these exports.

No operational blocker was found. The actual evidence supports publication of the complete negative formalization. This audit was performed by inspecting remote Linux execution and downloaded artifacts locally on macOS; it does not claim a local Linux rerun or external human peer review.
