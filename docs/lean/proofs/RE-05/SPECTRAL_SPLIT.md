# Accepted spectral split of the actual supplied basis

The actual selected singular-vector lookup defines an orthogonal projector.
Its complement equals the model's `complement` function and is self-adjoint
and idempotent. The selected and residual masks use exactly the full `U`
returned by the actual SVD, with the original strict threshold and its ties.
Positive singular directions agree on both SVD sides; zero directions remain
unconstrained.

Writing `H` for that actual residual projector and `R` for the actual leverage
matrix, the proof gives `threshold * I - H*R*H` positive semidefinite and the
corresponding quadratic-form bound. These statements need neither basis
independence nor positive accuracy: the square-root threshold is always
nonnegative. The actual residual basis blocks have Gram sum `H*R*H`.

Under the original basis-independence condition, the coefficient Gram matrices
of the actual selected and residual basis blocks are positive semidefinite,
sum to the identity, and are bounded by the identity. Each residual basis
member has Frobenius norm at most one. The Frobenius splitting uses the actual
supplied-order Gram–Schmidt family.

The independent [acceptance receipt](campaign-2026-10-26/independent-spectral-split-review/ACCEPTANCE.json)
records 22 fresh project producers, one positive consumer and three expected
rejection controls: 26 commands. It checks all 233 named project identities,
all 63 new declarations and the complete types of all 51 new theorems. The only
axioms are `propext`, `Classical.choice`, and `Quot.sound`. Separate author
replay and root source review are retained. All earlier frozen proof sources,
original inputs, 217 permanent IDs and TR-04's 205 package inputs remain exact.

This is deterministic geometry for the concentration proof. It does not prove
the Gaussian success probability or complete RE-05 target. RE-05 remains
**Solved**; no Linux/Comparator acceptance is claimed by this checkpoint.
