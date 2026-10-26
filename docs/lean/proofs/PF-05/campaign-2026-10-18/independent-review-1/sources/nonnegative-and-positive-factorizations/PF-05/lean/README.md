# PF-05 pre-proof Lean challenge

This is a statement review packet, not a formal proof. `Challenge.lean` has one
intentional `sorry` in the isolated Comparator hole. There is no `Solution.lean`
and no claim that PF-05 is Lean verified. The canonical status remains Solved.

The selected theorem is exactly `NLA.PF05.target : NLA.Statements.PF05.Target`.
The local `NLA/Statements/PF05.lean`, `NLA/Statements/Infrastructure.lean`, and
`Reviewed/PF05.lean` are byte-for-byte copies of the published reviewed
statement package. `SOURCE_LOCK.json` records their source paths and hashes,
plus the canonical README, preserved original, exact specification, and
mathematical proof source. `Check.lean` checks definitional equality of the
live and frozen propositions; this checks identity, not truth.

Before any proof implementation, two agents independent of the challenge
preparer must review the canonical target, full mathematical source,
`NUMERICAL_TARGETS.md`, imported definitions, this `Challenge.lean`, and its
Comparator signature. Reviews must bind the exact hashes and be retained in
`reviews/`. An approval for the earlier shared statement is useful evidence,
but does not review this new challenge packet. A substantive statement change
reopens both pre-proof reviews.

The source proof is Colbrook's Theorem 1, especially Theorem 8 for a nonzero
orthogonal pair. The finite-dimensional route still has substantial proof
obligations: rank-three spanning, operator representation and integration,
zero-row removal, normal form, the explicit feasible nonscalar direction,
and the positive-entry case from Dawson–Hoşten–Kubjas–Metsälampi Theorem 5.2.
All p, q, repeated and singular factors, zero entries and zero rows or columns
must remain covered. The positive-entry theorem cannot be left as an axiom.
No numerical certificate is needed for this mathematical proof.

The pinned Lean version is 4.33.1, Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert is
`621a43d7cf21f87872392a01e874f2f1dbddc926`. The copied manifest fixes
transitive package revisions. The intended local statement check is
`lake build Challenge Check` after the pinned Lean toolchain and packages are
available. Comparator cannot run before an independently reviewed full
`Solution.lean` exists.
