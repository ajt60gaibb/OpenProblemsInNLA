# MF-03 finite tableau tail to infinite cosine tail: pre-implementation contract

**Author:** `/root`, 10 October 2026. **Status:** awaiting independent mathematical/source review before Lean implementation. This is the exact last inequality in Gate 2 of the independently reviewed `SCHUR_PADE_ALL_ORDER_PRE_REVIEW.md`; it remains a tableau-sum statement until the finite dual Jacobi–Trudi identity and infinite determinant limit are proved.

For all naturals `N,m`, the existing exact finite tail is

```text
finiteCosineTail N m = Σ_{k : FiniteTailLabel N m} cosineFactor(k.val.val+1),
FiniteTailLabel N m = {k : Fin N // m≤k.val}.
```

The existing infinite tail is `cosineTail m = ∑' t:ℕ, cosineFactor(m+t+1)`. Prove the **exact comparison**

```text
finiteCosineTail N m ≤ cosineTail m.
```

This includes `N≤m` (empty finite label type and zero finite tail), `m=0`, and arbitrary finite `N`. The map `k ↦ k.val−m` embeds the finite labels into `ℕ`, and for every label `k≥m`, `m+(k−m)=k` exactly. All factors are strictly positive. The sequence `t ↦ cosineFactor(m+t+1)` is summable for every `m`: it is a tail of the summable positive factor sequence `k ↦ cosineFactor(k+1)` already established mathematically in `CosineCoefficientTransfer.lean` (the helper there is private, so the Lean implementation must reprove or expose summability without changing its frozen source). Thus a finite subseries is at most the whole `tsum`. No numerical approximation or stronger denominator hypothesis is needed.

In combination with the already kernel-checked `finiteAugTableauSum_le_rect_mul_tail`, nonnegative finite rectangle sums, and monotonicity of natural powers, prove the exact fixed-tail bound

```text
finiteAugTableauSum N m j ≤ finiteRectTableauSum N m * (cosineTail m)^j,
```

for every `N,m,j` with `j≤m`, including `j=0`. This is still an inequality between **finite weighted tableau sums**. The full MF-03 Target, determinant/tableau identities, and all-order Padé existence remain separate obligations. Preserve the canonical README, permanent ID, and frozen Lean Target unchanged.
