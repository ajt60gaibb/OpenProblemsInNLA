# RA-10 right orthogonal nuclear invariance: independent final review

**Accepted for aggregate import.** I independently reviewed the frozen
`NLA/Proofs/RA10/NuclearOrthogonalRight.lean`, SHA-256
`7e93f4c44d684645cc3354b847a95e56cd1c633936a0f86f9cb06d84482ed20e`,
against the approved exact precontract and original `RA10.NuclearNorm`.

The sole public theorem has precisely `U * U.transpose = 1` and
concludes equality of the frozen complete `Fin n` singular-value sums
for `X*U` and `X`, with arbitrary real square `X,U` and `n=0`. Its
Gram matrix calculation preserves noncommutative order; the pinned
`Matrix.charpoly_mul_comm` moves the final `U` to the front and the
single hypothesis reduces `UUᵀ` to one. The proof transfers the resulting
charpoly equality to real Euclidean linear maps, matches the ordered
Gram eigenvalues at every original index, then takes square roots. It
does not assume `UᵀU=1`, invertibility, positivity, or an ideal bound.

The separate imported exact-signature audit
`/private/tmp/ra10-nuclear-orthogonal-right-independent-audit.lean`,
SHA-256 `20777fcd3b60bb0db02c3577f37c5690c18542320fd4a7115662d751fd032bd4`,
passed pinned Lean 4.33.1 with LeanCert `kernel`. Its `#assert_trust kernel`
passed and `#print axioms` reported only `[propext, Classical.choice,
Quot.sound]`. Source inspection found no `sorry`, `admit`,
`native_decide`, `unsafe`, or new axiom. Two-sided invariance,
coefficient-one ideal inequalities, pinching, Eq. (14), and the full
RA-10 Target remain open.
