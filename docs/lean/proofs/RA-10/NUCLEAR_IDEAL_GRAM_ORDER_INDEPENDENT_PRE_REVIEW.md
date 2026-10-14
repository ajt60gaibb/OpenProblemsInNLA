# RA-10 sharp Gram order for nuclear ideal: independent pre-review

**Disposition:** approved for implementation of the exact displayed
theorem. I independently reviewed
`NUCLEAR_IDEAL_GRAM_ORDER_PRE_REVIEW.md` at SHA-256
`c047c4b8204fafd28a1a99e108484aa2c99e90f4b8910d5ae309a755c7b9555d`
and verified all seven source locks against the repository.

With the pinned `Matrix.Norms.L2Operator` scope, `‖X‖` is exactly the
Euclidean induced operator norm. The proposed frozen custom PSD matrix
has the correct order and coefficient:
`‖X‖² • (YᵀY) − (XY)ᵀ(XY)`. Its quadratic form at any real vector `x`
is `‖X‖²‖Yx‖²−‖X(Yx)‖²≥0` by the operator norm inequality, with no
commutation or invertibility assumption. Each real Gram matrix is
symmetric, so the scalar difference satisfies both conjuncts of the
frozen predicate. This covers zero matrices and `Fin 0` and retains
coefficient one.

This review approves only the Gram PSD gate. A frozen implementation,
separate imported exact-signature/axiom audit, and LeanCert-kernel check
are required before aggregate import. Gram eigenvalue transfer, the
nuclear ideal inequalities, Eq. (14), and full Target remain open.
