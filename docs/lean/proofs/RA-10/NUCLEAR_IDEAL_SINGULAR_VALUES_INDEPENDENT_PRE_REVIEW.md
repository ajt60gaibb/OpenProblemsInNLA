# RA-10 Gram spectra and sharp left nuclear ideal: independent pre-review

**Disposition:** approved for the proposed staged Lean implementation. I independently reviewed `NUCLEAR_IDEAL_SINGULAR_VALUES_PRE_REVIEW.md` at SHA-256 `4a9f5a77af38dda29562f5b50cb9d9109f7633b8c1cc76f9efd6d042fc7902fd` and checked every repository and pinned Mathlib source lock.

The frozen nuclear norm is the sum of **all** `Fin n` values `singularValues i.val` of `Matrix.toEuclideanLin`; the scoped `‖X‖` is the Euclidean induced operator norm. The first proposed equality identifies each supplied ordered PSD Gram eigenvalue with the square of the singular value at the same zero-based index. Pinned `LinearMap.sq_singularValues_fin` supplies this eigenvalue in descending order; `Matrix.IsHermitian.eigenvalues₀` and the existing `sortedHermitianIndex` must be used to match the matrix and operator indexing. An unsorted eigenvalue multiset would not suffice. The proposed pointwise inequality and its sum have coefficient one, the correct left product `X*Y`, and no omitted zero/tied singular value or dimension factor.

The Gram subtraction is `(‖X‖²)•(YᵀY)−(XY)ᵀ(XY)`, so the already audited ordered Loewner theorem gives the required direction after a scaled ordered decomposition. The nonnegative square-root and finite-sum steps retain the same constant, including `X=0`, `Y=0`, and `Fin 0`. The source Eq. (14) and full RA-10 Target remain separate obligations.

This is source-level approval only. Each exact public declaration still requires a direct pinned LeanCert kernel check, frozen source SHA, and independent imported exact-signature/source/axiom audit before aggregate import. No unproved premise may substitute for the Gram-index equality or scaled decomposition.
