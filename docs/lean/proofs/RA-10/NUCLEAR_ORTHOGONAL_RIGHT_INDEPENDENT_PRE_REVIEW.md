# RA-10 right orthogonal nuclear invariance: independent pre-review

**Disposition:** approved for implementation of the exact displayed
theorem. I independently reviewed
`NUCLEAR_ORTHOGONAL_RIGHT_PRE_REVIEW.md` at SHA-256
`7f56e1defbbd1476291e9e132ade44699f8fe583b9a8d012962fee414e8610b2`
and verified all six source locks against the repository.

For arbitrary real `X,U`, the sole hypothesis `U*U.transpose=1` gives
the required cyclic characteristic-polynomial identity for the Gram
matrix of `X*U`:
`charpoly(Uᵀ (XᵀX) U)=charpoly((UUᵀ)(XᵀX))=charpoly(XᵀX)`.
The order is correct and uses no commutation of `X` and `U`.
Matching sorted Gram eigenvalues before square roots gives equality at
every original singular-value index, including ties and zeros; the
`Fin 0` case has empty sums. This argument needs no extra
`U.transpose*U=1` premise. The frozen `NuclearNorm` and its complete
`Fin n` sum remain unchanged.

Approval is mathematical/source-level only. Freeze the implementation
for an independent imported exact-signature, LeanCert-kernel, and axiom
audit before aggregate import. Two-sided invariance, nuclear ideal
inequalities, pinching, Eq. (14), and the full Target remain open.
