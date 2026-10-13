# RA-10 left orthogonal nuclear invariance: independent final review

**Accepted for aggregate import.** I independently reviewed the frozen
`NLA/Proofs/RA10/NuclearOrthogonalLeft.lean` at SHA-256
`55e08063ce32da702db380e9d82315517b65d28082c0504f33919bc4f91146ba`
against the approved precontract and the frozen `RA10.NuclearNorm`.

The only public result has exactly the stated `U.transpose * U = 1`
hypothesis and concludes equality of the original all-`Fin n`
singular-value sums for `U*X` and `X`. The proof uses the exact
matrix-to-Euclidean-operator multiplication and transpose/adjoint bridges,
obtains equality of the two Gram operators, then matches every sorted
Gram eigenvalue at the same `Fin n` index before applying `Real.sqrt`.
It covers arbitrary `X`, ties, zeros, and `n=0`, with no right-orthogonal
premise or alternate norm.

The separate imported exact-signature audit
`/private/tmp/ra10-nuclear-orthogonal-left-independent-audit.lean`,
SHA-256 `a8848e07ed0fdf9acadb72a4764ca3dae4f227828394e0ce973292b69481cc3e`,
passed pinned Lean 4.33.1 with LeanCert `kernel`; `#print axioms`
reported only `[propext, Classical.choice, Quot.sound]`. The source has
no `sorry`, `admit`, `native_decide`, `unsafe`, or new axiom. Right
invariance, nuclear ideal inequalities, pinching, Eq. (14), and the
full RA-10 Target remain open.
