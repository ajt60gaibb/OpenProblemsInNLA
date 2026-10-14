# RA-10 two-sided orthogonal nuclear invariance: independent final review

**Accepted for aggregate import.** I independently reviewed frozen
`NLA/Proofs/RA10/NuclearOrthogonalConjugation.lean` at SHA-256
`f56ca9699037e9e42b7590ea0efce71e792cebc8ece832eac1b57ae56a50ffe7`
against the exact signature already independently approved in
`NUCLEAR_PINCHING_GATE_PRE_REVIEW.md`. The public theorem retains both
`UᵀU=1` and `UUᵀ=1` arguments and concludes the frozen complete
singular-value sum identity for `U*M*Uᵀ` at every `n`, including zero.
The proof first applies independently audited right invariance to
`(U*M)*Uᵀ` and then left invariance to `U*M`. The right theorem for
`Uᵀ` requires `UᵀᵀUᵀ=1`, exactly the supplied `UᵀU=1`; the second
source hypothesis remains explicitly present. No matrix order,
singular-value cutoff, or norm is changed.

The separate imported exact-signature audit
`/private/tmp/ra10-nuclear-orthogonal-conjugation-independent-audit.lean`,
SHA-256 `5162c9adeedf7d272743635a10cf2767d08898908171248604b7294af77c7cbb`,
passed pinned Lean 4.33.1 and LeanCert `kernel`; only `[propext,
Classical.choice, Quot.sound]` were reported. The source contains no
`sorry`, `admit`, `native_decide`, `unsafe`, or new axiom. Nuclear triangle,
pinching contraction, ideal inequalities, Eq. (14), and full RA-10
Target remain open.
