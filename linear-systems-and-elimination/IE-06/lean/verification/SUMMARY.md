# Verification record — complete IE-06 proof, 2026-10-06

[Solution.lean](../Solution.lean) proves the complete original IE-06
square-root upper-exponent limit and the stronger all-Schur tail bound, with
all probabilistic estimates supplied by proved declarations. The final fresh
local build, exhaustive project-declaration axiom audit, and actual six-target
Challenge/Solution comparison **passed**. The subsequent full authoritative
Linux Comparator/exporter/kernel-replay route also **passed**.

## Authoritative Linux CI acceptance

[Run 37513136002](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002) /
[job 112439363988](https://github.com/ajt60gaibb/OpenProblemsInNLA/actions/runs/37513136002/job/112439363988) accepted the actual IE-06
solution at tested merge commit `6091e87aa8538ea31df21fd06cce3d9e42f65c2a`,
for PR head `05b1c83e11042d7067cd51c5a4bfc0265e7390f4`. The retained
[result](linux-ci-2026-10-06/verify-20261006T184228Z-4239/result.json) has SHA-256
`e8d6ccc4501c435ca30d48bb8b9940ce6bcba9417b884b9625f4414ef102f168`.
The complete small artifact is retained unchanged beside its
[provenance and verification guide](linux-ci-2026-10-06/README.md).

| Authoritative check | Result and evidence |
| --- | --- |
| Full actual-target Comparator | PASS: [log](linux-ci-2026-10-06/verify-20261006T184228Z-4239/comparator.log) builds and exports Challenge and Solution, accepts the six exact targets and their referenced definitions, and accepts the exported solution through Lean's default kernel. |
| Permitted proof axioms | Exactly `propext`, `Classical.choice`, and `Quot.sound`; no replaceable definition holes. |
| Actual Linux isolation | PASS: [sandbox probes](linux-ci-2026-10-06/verify-20261006T184228Z-4239/sandbox.log) exercise non-root build/export isolation, write restrictions, private namespaces, network/AF_UNIX restrictions, and rejection of unsupported sandbox options. |
| Replay and Comparator regressions | PASS: [three replay controls](linux-ci-2026-10-06/verify-20261006T184228Z-4239/kernel-controls.log) and [five Comparator cases](linux-ci-2026-10-06/verify-20261006T184228Z-4239/comparator-controls.log). |
| Forbidden-proof rejection | PASS: [sorry](linux-ci-2026-10-06/verify-20261006T184228Z-4239/negative-sorry.log) and [native](linux-ci-2026-10-06/verify-20261006T184228Z-4239/negative-native.log) exit 1 at forbidden-axiom detection as required. |
| Identity before promotion | PASS: [all 1,139 recorded inputs](linux-ci-2026-10-06/input-identity-before-promotion.json) matched the promotion checkout before documentation edits. |

The Linux run covers the six selected targets and their exported dependency
closure. The earlier local audit below separately covers every owned declaration.
The tested proof sources, comparator configuration, dependency pins, frozen
reviews, and historical receipts remain unchanged. Current status documents and
metadata were updated after CI, and the new evidence directory was added; neither
is misrepresented as part of the old CI snapshot. The retained delivery manifest
continues to describe its historical publication snapshot. The CI command's
`semantic_review` value remains `not-performed-by-this-command`; mathematical
fidelity rests on the separately recorded reviews.

## Earlier local validation

The accepted [execution receipt](local/attempt-0i_0ibma/result.json) has SHA-256
`50fbaf7b84715f7fdf4e28d3813abb4c2f7837514f9322c255cb99fa1b0952e2`.
It binds the source snapshots, Lean executable, dependency pins, command logs,
Comparator sources, and generated checking programs. The coordinator's
[separate receipt audit](root-final-receipt-audit.json) rechecked all 121
source/configuration hashes against both the snapshots and current files,
all 122 command-log hashes, and every command's expected outcome.
An [independent execution review](../reviews/final-validation-independent-review.md)
also verified the source coverage, generated checks, exact Comparator results,
dependency pins, and all retained logs.

| Check | Result and evidence |
| --- | --- |
| Fresh project-source build | PASS: all 114 Lean source modules compiled in the accepted receipt. |
| Every concrete project declaration | PASS: [axiom audit](local/attempt-0i_0ibma/AuditConcrete.lean.log) covers 3,229 declarations, including private/generated auxiliaries, across 113 concrete modules. Only `propext`, `Classical.choice`, and `Quot.sound` occur transitively. |
| Final LeanCert kernel assertions | PASS: all six exports in [Solution](local/attempt-0i_0ibma/Solution.lean.log), with only the three permitted foundational axioms. |
| Actual exact-target Comparator | PASS: [comparison log](local/attempt-0i_0ibma/CompareSolution.lean.log) records a statement/referenced-definition check and a proof-axiom check for each of the six actual theorems. Challenge and Solution were loaded into separate environments. No definition holes are allowed. |
| Sorry/native rejection | PASS: [admitted proof](local/attempt-0i_0ibma/RejectSorry.lean.log) and [native execution](local/attempt-0i_0ibma/RejectNative.lean.log) were both rejected as required. Their nonzero exits are expected successes of the controls. |
| LeanCert numerical kernel fixture | PASS: [fixture log](local/attempt-0i_0ibma/KernelControl.lean.log), proving exact `log(2) < 7/10`. This tests infrastructure and is not used in the Gaussian-growth proof. |
| Unchanged Comparator rejection fixtures | PASS: [nine actual core-library assertions](comparator-core/attempt-yx_mpi_g/RunCore.lean.log), including changed-type, changed-definition, kind, and forbidden-axiom rejection; [receipt](comparator-core/attempt-yx_mpi_g/result.json). |
| Shared harness regressions | PASS: [12 tests](shared-harness-tests.json). Shared acceptance safeguards were not modified. |
| Permanent IDs and repository regressions | PASS: [record](final-repository-checks.json), validating 217 IDs against `origin/main`, all 17 permanent-ID tests, and all 30 Lean-selection/metadata tests. |
| Completed-proof metadata | PASS: [final documentation/schema receipt](../reviews/final-documentation-validation.json) validates the v0.4 metadata with all six results selected exactly once by Comparator. |
| Prepublication canonical preservation | PASS: at the recorded local validation, the canonical IE-06 README, TeX, and PDF matched their initial working hashes. Publication subsequently adds evidence links and regenerated documents while preserving the complete original target. Both original source pages remain verbatim copies. |

The six comparisons cover `squareRootUpperBound`, `schurSubpolynomialTail`,
`gaussianMatrix_probability`, `exceedanceEvent_measurable`,
`admissiblePath_exists`, and `gaussianMatrix_singular_null`, all in namespace
`NLA.IE06`. The proof imports no Challenge declarations. The frozen Challenge
retains its six deliberate reference placeholders and historical statement-phase
header; these are excluded from the concrete-proof audit. The successful build
emitted those six expected reference warnings and 79 nonfatal warnings in
vendored supporting modules. The concrete proof has no admitted declaration or
unproved literature axiom.

The [final independent mathematical scope review](../reviews/final-independent-mathematical-scope-audit.md)
checks the original statement, actual independent standard Gaussian law,
all Schur stages, input normalization, every admissible tie choice, adaptive
conditioning, and the full quantifiers in both final bounds. It is bound to
the final source hashes. Additional independent source/build reviews,
preimplementation mathematical specifications, adopted-proof provenance, and
licenses are retained under `reviews/` and `source/`. These are AI-agent
reviews; no human peer review or manuscript-author endorsement is claimed.

The manuscript's displayed Theorem 1.4 uses LU growth. This formalization
proves the stronger all-Schur estimate developed in its Section 5 argument,
with the required elimination, normalization, and almost-sure tie bridges.
It does not infer all-Schur control from an LU-only statement or claim to
formalize every theorem in the manuscript. The exact proof chain and reviewed
alternative intermediate bounds are described in [PROOF_STATUS.md](../PROOF_STATUS.md).

Local verification uses Lean 4.33.1 and the pinned existing dependency object
cache. Project sources were rebuilt freshly; dependency revisions and tracked
source cleanliness were checked before and after. That historical local run
did not execute the authoritative Linux sandbox, exporter, or raw-kernel replay.
The subsequent CI run above completed those gates. The original local receipt
retains its false flags; its scope is not retroactively enlarged. [INFRASTRUCTURE.md](../INFRASTRUCTURE.md)
gives both reproduction paths and their trust boundaries.

This record supersedes the initial statement-only status. Historical receipts
and reviews remain available and certify only their recorded snapshots. The
[delivery manifest](delivery-manifest.json) records the historical publication
package hashes; it is preserved unchanged and excludes the subsequent CI evidence
and status-document updates. It is an integrity inventory, not a proof checker.

At the completion of the retained local validation, nothing had been committed,
pushed, submitted to remote CI, or sent to John Urschel by the agents. The
maintainer subsequently reported permission to publish and authorized the push;
[the publication record](../PUBLICATION.md) documents that later step. Historical
receipts retain their original publication flags. The original dirty checkout
was preserved, and publication was prepared on an isolated branch.
