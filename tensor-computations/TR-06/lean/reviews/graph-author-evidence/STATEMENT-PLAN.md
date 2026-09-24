# Graph-Jacobian statement boundary for independent pre-proof review

Authorship: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. Original TR-06 mathematical proof remains attributed to Matthew J. Colbrook. This is a supporting inequality proposal, with no completed proof claim.

Exact draft: `NLA/TR06/GraphJacobian.lean`, SHA-256 `78c9b8dd1fbdcf6368563de240ed3d45641f0a66217d4d02dcf8bebe225ced3b`. Its map definitions and both universal propositions typecheck under pinned Lean 4.33.1 without placeholders or new axioms. No theorem proof has been implemented.

All spaces E,F,G are real finite-dimensional inner-product spaces, with their inner-product norms; no dimension lower bound is imposed. The paired map is explicitly

```lean
pairedL2Map (A : E →L[ℝ] F) (B : E →L[ℝ] G) : E →L[ℝ] WithLp 2 (F × G)
```

constructed by composing `A.prod B` with the inverse `WithLp.prodContinuousLinearEquiv 2 ℝ F G`. Thus its value is literally `WithLp.toLp 2 (A x, B x)` and the output squared norm is the sum of the two squared norms. `graphL2Map T := pairedL2Map (ContinuousLinearMap.id ℝ E) T`.

The first proposed theorem signature is:

```lean
theorem opNorm_le_normDet_graphL2Map (T : E →L[ℝ] F) :
    ‖T‖ ≤ (graphL2Map T).toLinearMap.normDet
```

The range-inverse operator is exactly

```lean
def rangeInverseOperator (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hA : Function.Injective A) : LinearMap.range A.toLinearMap →L[ℝ] G :=
  B.comp (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv.symm.toContinuousLinearMap
```

The range uses the inherited F inner product and norm. This is the same construction as frozen `inducedDerivative`, generalized to arbitrary finite-dimensional Hilbert inputs/outputs. The second signature is:

```lean
theorem opNorm_rangeInverseOperator_mul_normDet_le
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (hA : Function.Injective A) :
    ‖rangeInverseOperator A B hA‖ * A.toLinearMap.normDet ≤
      (pairedL2Map A B).toLinearMap.normDet
```

Both statements remain valid in dimension zero: the operator norm is zero and the norm determinant of a zero-dimensional domain map is one. The injectivity premise in the second statement is an actual property of A, not a volume or derivative-bound premise.

## Proposed proof route and pinned APIs

The first inequality can use an orthonormal eigenbasis of `T.adjoint ∘ₗ T`, with nonnegative eigenvalues lambda_i. In this basis the graph Gram matrix is diagonal with entries 1+lambda_i. Therefore `normDet graph ^ 2 = product_i (1+lambda_i)`. Each factor is at least one, so the product bounds every lambda_i. The eigenbasis expansion gives `‖T x‖² = sum_i lambda_i * coeff_i²`, hence `‖T x‖² ≤ normDet graph² * ‖x‖²`, then the operator norm bound. This avoids a missing ready-made operator-norm/singular-value equality. Empty bases obey the same finite-sum/product identities.

Available pinned APIs include `LinearMap.IsSymmetric.eigenvectorBasis`, `apply_eigenvectorBasis`, `eigenvectorBasis_apply_self_apply`, `LinearMap.isPositive_adjoint_comp_self.nonneg_eigenvalues`, `OrthonormalBasis.sum_repr`, `sum_inner_mul_inner`, `sum_sq_inner_right`, `LinearMap.normDet_sq_eq_det_gram`, `Matrix.det_diagonal`, and `WithLp.prod_inner_apply`. An alternative route uses `LinearMap.normDet_eq_prod_singularValues`, but the eigenbasis route appears more direct because no existing singular-value/operator-norm equivalence was found.

For the second inequality, factor the paired map as the range-restricted A, followed by the graph of `rangeInverseOperator`, followed by the L2 isometric inclusion `range(A) × G → F × G`. Norm determinants multiply for the first factor because its domain and codomain have the same dimension; the final inclusion has norm determinant one and preserves graph norms. The required APIs are `LinearMap.normDet_comp_of_finrank_eq`, `LinearMap.normDet_codRestrict`, `LinearIsometry.normDet_eq_one`, and `LinearIsometry.withLpProdMap` (available directly in pinned ProdLp.lean). The factorization uses an exact inverse of A on its range, so no arbitrary inverse outside the range or totalized derivative is introduced.

These inequalities are only linear graph-Jacobian estimates. They do not assume or prove the nonlinear area formula, finite graph volume, semialgebraic regularity, radial integration, or finite expectation. They leave frozen Definitions and Challenge untouched and need no numerical computation.
