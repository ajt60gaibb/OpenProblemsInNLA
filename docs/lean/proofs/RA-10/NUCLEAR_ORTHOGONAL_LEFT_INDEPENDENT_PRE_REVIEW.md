# RA-10 left orthogonal nuclear invariance: independent pre-review

**Disposition:** approved for implementation of the exact displayed theorem.
I independently reviewed `NUCLEAR_ORTHOGONAL_LEFT_PRE_REVIEW.md` at SHA-256
`626b9d76a21d7aa0dd759a9758adf87be4c9e450408406d9e3d19a09dd0cfff8`
and verified its five source hashes against the repository.

The frozen `NuclearNorm` sums every `Fin n` singular value of the real
Euclidean linear operator, including the empty sum at `n=0`. The hypothesis
`U.transpose * U = 1` makes the Gram operator of `U*X` equal to that of
`X` in the correct multiplication order: `(UX)ᵀ(UX)=Xᵀ(UᵀU)X=XᵀX`.
Thus corresponding sorted Gram eigenvalues and their square-root singular
values agree at the same index, even with ties or zeros. The one-sided
hypothesis is sufficient, and the proposed theorem adds no hidden
symmetry, positivity, inverse, dimension, or right-orthogonality condition.

This review approves only left orthogonal invariance. A frozen source,
separate imported exact-signature audit, `#assert_trust kernel`, and axiom
check are required before aggregate import. Right invariance, nuclear
ideal inequalities, Eq. (14), pinching, and the full RA-10 Target remain
open.
