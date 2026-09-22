# TR-27 final fidelity review: verification completion

Reviewer: `/root/tr27_final_fidelity`, independent Codex AI referee, author of none of the mathematical source or definitions. Phase: completion of the mechanical gates left pending in [my original source review](final-fidelity-referee.md). I did not operate the Linux verification. This is an independent review of its actual retained evidence and its correspondence to the previously reviewed source, not a second Linux execution, human peer review or official Tau Ceti endorsement.

**Verdict: APPROVE.** The source approval and now-completed authoritative gates support the complete original TR-27 negative answer: rank 3, border rank at most 2, and ordinary full-Segre tensor-square rank 9. No mathematical correction or additional fidelity gate is requested. The original source review and receipt remain byte-identical; this separate addendum closes their explicitly pending Linux, LeanCert, Comparator and axiom-evidence checks.

## Independent binding of the actual run

I read the complete actual Comparator log, every sandbox/kernel/Comparator/forbidden-axiom control log, both dependency preparation logs, input/result/dependency/tool receipts, capture/launcher/verification source, execution and service provenance, and the final operational report. I did not use the operator's PASS summary as a substitute for those records. The operator explicitly identifies authorship of ProjectiveGeometry and does not claim to be its independent mathematical referee.

My independently written [evidence audit](final-fidelity-completion-evidence/audit.py) and its [machine-readable results](final-fidelity-completion-evidence/audit.json) passed. It checks every one of the **116** project input files against the actual Git blobs at publication commit `775e8b169119c4045b07db7666eda8c001ae3bd1`, the transferred input archive, the retained source snapshot, the unchanged live package, preparation/dependency/verification receipts, and every hash in my earlier source review. This includes Definitions, all proof modules, Solution, Challenge, the entire frozen numerical target, the 25-target Comparator configuration and build pins. The four preproof boundary hashes still match their freeze. No mathematical bytes changed.

The result's guest commit `59f8e715525a25cce2e4767a1372a94650c8071c` is intentionally different: it is a fresh verification-only repository with precisely the same project bytes. I checked that relation rather than mistaking it for the publication commit. The 116-file SHA256 maps are equal across the independent Git/archive comparisons and all input receipts. Neither the input archive nor the tracked source includes project `.lake` contents or compiled objects. The preserved evidence archive also matches every extracted member. The original report and receipt still have hashes `8281caf77d7372b8cd8f647e3ef28e9f3fd2cd398020356179664f272c867def` and `d55240bbca3c33f6d63bbaea493cd5246b1c0c7eb7c765cb4040a093ef2cbc35`.

## What the logs establish

The successful run was non-root Linux UID 1000, with the supported systemd/Bubblewrap/Landrun isolation. It began at 19:24:08 UTC and finished at 19:26:34 UTC on 22 September 2026. The retained runner and actual verifier logs exit zero. The bootstrap receipt records an earlier kernel version; the separate runtime record identifies the current kernel and the fresh controls executed on it. The documented unprivileged-user-namespace prerequisite was restored before verification. That preparation did not remove or replace any sandbox assertion.

The actual log builds Challenge separately, with exactly its 25 intentional specification-placeholder warnings. It then builds every proof module, the authentic `LeanCert.Tactic.Verification`, and Solution. There is no Solution warning or unresolved proof. Both logged module export lists contain exactly the 25 required declarations, including `projective_counterexample` and `original_conjecture_false`, in the frozen order. The configuration has no definition holes. The actual Comparator reports default-kernel acceptance and `Your solution is okay!`, with exit zero, after those exports. The shared harness source confirms that it checks immutable inputs before and after dependency preparation and comparison, and that it does not build Solution before Comparator.

For every selected declaration, Solution's explicit printed transitive axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`. The source sets `leancert.trust` to `kernel` and contains a corresponding `#assert_trust kernel` for each of those same 25 names; successful elaboration therefore executed all of them. I inspected the retained authentic LeanCert implementation: the command collects transitive axioms and rejects sorry, custom and native-compiler dependencies for kernel trust. Its hash is bound to the pinned dependency's Git blob by the read-only capture. Exact algebra needs no interval certificate, and none is represented as having been used.

All ten dependency checkouts are logged at the exact manifest revisions, and their captured actual Git HEADs agree. Lean is 4.33.1; LeanCert is `621a43d7cf21f87872392a01e874f2f1dbddc926`; Mathlib is `0df444a360eaa60ab8c11dca51a86af692955474`. The verifier sources match the publication's shared harness. Its authenticated source lock pins Forsythe `8d1b0c0545a77b40245e84705aa7d273e6c81e62`; validated_tools checks the locked source bytes, binary hashes, strict adapter/probe environment and Lean version before running the controls. The retained strict adapter hash agrees with that lock. The Mathlib log transparently records use of its supported pinned cache, not a complete from-source rebuild of all library objects.

## Controls and limits checked

The build and export sandbox modes both ran: prohibited writes/truncations/creation and symlink escape outside the build area failed; the permitted build write succeeded and export writes failed; all six relevant namespaces were private; host-process access, loopback and AF_UNIX access were denied; capabilities were empty and no-new-privileges was set. Four unsupported or excessive writable-path options were rejected. The nested namespace attempt actually launched and failed at UID-map setup; I do not interpret that as a successful entry into a nested namespace followed by an inner write.

The raw-kernel controls accepted the honest inductive/quotient proof, rejected the raw True proof offered at False, and rejected the quotient post-check mismatch. All five retained Comparator controls produced their intended outcomes. In particular the fixture named `simple_kind_mismatch` actually reports an illegal helper axiom, while the separate `type_mismatch` fixture reports a theorem-statement mismatch. The dedicated sorry and native controls failed with the expected forbidden `sorryAx` and `checked._native.native_decide.ax_1_1`, respectively. These expected failures are evidence of enforcement, not failed TR-27 runs.

Pinned Comparator removes its intermediate raw export streams. I inspected the full logged export lists, successful comparison/axiom result and actual default-kernel replay; I do not claim to have read nonexistent retained streams. I independently ran only the local evidence/hash/Git/archive audit, not Lean or the Linux verifier. Those limits are explicit in the [completion receipt](final-fidelity-completion-receipt.json).

## Publication notice and preserved scope

I approve the proposed canonical verification notice at the hash below for scope, attribution and evidence wording. It states the negative answer, unrestricted complex decompositions, full zero-locus geometry and separate tensor factors, credits George Stepaniants with the requested Caltech affiliation and substantial AI assistance, and preserves Matthew J. Colbrook's original mathematical authorship. It does not add a contact email or claim human peer review or official Tau Ceti endorsement. It expressly leaves smoothness, exact border rank 2 and arbitrary finite delays at their manuscript scope. The initial missing direct completion-report links were corrected; the immutable old reports remain unchanged.

Apply the notice after the other independent referee's completion approval. Later README/metadata status updates and these completion addenda must not be represented as inputs of this earlier run. The archived pending metadata is correctly historical. My source-level scope conclusion is unchanged, and the permanent canonical problem statement and ID remain the same target.

## Evidence identity

The detailed 116-input map and checks are in the independent audit JSON; the completion receipt records every listed evidence hash and the notice hash. The key files below are relative to `verification/linux/`.

| Evidence | SHA256 |
| --- | --- |
| `successful-verification/comparator.log` | `fa097adc33fe3d9b8bd0863a27d9a1dcd2df8503117dcd733a50eadf6f47c938` |
| `successful-verification/result.json` | `4589f4f49d2e63b30453c1a6791dc38f5733c6f04b271bf8bd4c396aeceb5201` |
| `input-receipt.json` | `eda0ac53ffb91ebd1a894c553a56923d01d74df4ccdf78b30ed2d0c62b054958` |
| `input.tar` | `ac04194757cbaaab666b4ae2f654a2d48078cd13f2c08a7a2eab32b0d3adb4c6` |
| `verification-evidence.tar.gz` | `2a0e455491252b3b6766ba25dc566c924298868a07fa60126b23dd77f677f580` |
| `dependency-evidence/LeanCert-Verification.lean` | `2c576708b528acdde17796b0b715b83079f9cad377182dbd87c248323ff0a58c` |
| `checker-source/source-lock.json` | `b3833b07916e5db77579b9cc53ca582282f6a841f36d6a60d693e5b02d342b6b` |
| `OPERATIONAL-REVIEW.md` | `15bad3fdd90115149b76d2f30e207d164ca65f5d5e74547031ffa38e54595ab2` |

Proposed canonical notice SHA256: `b437f33b4527829046cd85059a5cb324c7d905fc2630fb983023333db796d1f2`.
