# MF-03 finite elementary determinant limits: pre-implementation contract

**Author:** `/root`, 10 October 2026. **Status:** awaiting independent mathematical review before Lean implementation. This is the fixed-size determinant continuity part of Gate 3 of the approved all-order Schur–Padé contract. It does not assert the dual Jacobi–Trudi tableau identity or determinant positivity.

Use the exact already reviewed `finiteCosineElementaryCoeff N n`, which sums products of the first `N` zero-based cosine factors over cardinality-`n` subsets of `Finset.range N`, and the original `cosineElementaryCoeff n`. For every `N,m,j:ℕ`, define the **real** matrices and determinants with `r,c:Fin m`:

```text
finiteCosineRectDet N m
  = det (fun r c => finiteCosineElementaryCoeff N (m+c.val-r.val)),
finiteCosineAugDet N m j
  = det (fun r c => finiteCosineElementaryCoeff N
      (m+(if r.val<j then 1 else 0)+c.val-r.val)),
cosineRectDet m
  = det (fun r c => cosineElementaryCoeff (m+c.val-r.val)),
cosineAugDet m j
  = det (fun r c => cosineElementaryCoeff
      (m+(if r.val<j then 1 else 0)+c.val-r.val)).
```

Natural subtraction is exact here: since `r.val<m`, every `m+c.val-r.val` and augmented index is nonnegative with no unintended truncation. The first `j` rows are shifted by exactly one in the augmented matrix. Prove the exact fixed-size limits

```text
Tendsto (fun N => finiteCosineRectDet N m) atTop (nhds (cosineRectDet m)),
Tendsto (fun N => finiteCosineAugDet N m j) atTop
  (nhds (cosineAugDet m j)),     j≤m,
```

and the exact zero-row identities `finiteCosineAugDet N m 0=finiteCosineRectDet N m` and `cosineAugDet m 0=cosineRectDet m`. The limits hold for `m=0` and its only permitted `j=0`; the empty determinant is one. Each matrix entry converges by the independently reviewed coefficient-limit theorem; determinant is a polynomial in the fixed `m²` entries. No numerical determinant is evaluated. These limits alone neither imply determinant positivity nor identify the determinants with weighted tableaux; those remain independent proof obligations. Preserve the canonical README, permanent ID, and frozen Lean Target.
