# MF-03 dense-set cosine product: pre-implementation contract

This contract isolates the first implementable part of the manuscript's
cosine-product bridge. It is a mathematical and numerical specification for
independent review. It asserts no Lean proof and changes neither the frozen
`NLA.Statements.MF03.Target` nor the canonical MF-03 problem.

## Exact proposed interface

In a new, initially unimported `NLA.Proofs.MF03.CosineDenseProduct` module,
import the existing reviewed `CosineProduct.lean` and pinned Mathlib Euler
sine-product and cosine-series results. Export these two theorems in namespace
`NLA.Proofs.MF03`:

```lean
theorem waveSeries_neg_pi_sq_eq_cos (w : ℂ) :
    waveSeries (-(((Real.pi : ℂ) * w) ^ 2)) =
      Complex.cos ((Real.pi : ℂ) * w)

theorem cosinePartialProduct_tendsto_waveSeries_of_sin_ne_zero
    (w : ℂ)
    (hw : Complex.sin ((Real.pi : ℂ) * w) ≠ 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        cosinePartialProduct N (-(((Real.pi : ℂ) * w) ^ 2)))
      Filter.atTop
      (nhds (waveSeries (-(((Real.pi : ℂ) * w) ^ 2))))
```

The only extra premise is `sin(πw)≠0`, required for the finite-ratio
argument. It is not an assumption on the final MF-03 Target. The target
quantifies over every `m≥1`, every reduced normalized Padé pair, and every
complex `z` with `‖z‖≤3`; neither proposed theorem claims that conclusion.

## Exact factor, index, and coefficient checks

`CosineProduct.lean` already defines
`cosinePartialProduct N z=∏_{k=0}^{N-1}(1+cosineFactor(k+1)z)` and
`waveSeries z=∑_{j≥0}z^j/(2j)!`. For `z=−(πw)^2`, the `k`th factor is

```text
1 + cosineFactor(k+1) z
  = 1 − 4w²/(2k+1)².
```

Here `cosineFactor(k+1)=1/[π²(k+1/2)²]=4/[π²(2k+1)²]`; the first factor
(`k=0`, `ν=1`) is `1−4w²`. There is no `ν=0` factor. At `N=0`, the empty
product is one. As a sign check, `w=1/2` gives
`z=−π²/4`: the first factor and `cos(π/2)` are both zero, and the sine
premise holds. These are exact identities, with no rounded constants.

Pinned `Complex.cos_eq_tsum` states
`cos u=∑_{j≥0}(-1)^j u^(2j)/(2j)!`. With `u=πw`, the exact power identity
`(−u²)^j=(−1)^j u^(2j)` proves the first theorem. Its `tsum` equality is
backed by Mathlib's `Complex.hasSum_cos`; coefficient matching alone without
summability is insufficient.

## Finite even/odd splitting and limit

Set

```text
S_N(w) = ∏_{j=0}^{N-1} (1−w²/(j+1)²),
C_N(w) = ∏_{k=0}^{N-1} (1−4w²/(2k+1)²).
```

The exact finite parity reindexing is
`S_(2N)(2w)=S_N(w)·C_N(w)`. Even denominator indices `2,4,…,2N`
produce `S_N(w)`; odd indices `1,3,…,2N−1` produce `C_N(w)`.
`C_N(w)` is termwise equal to the proposed `cosinePartialProduct` value.
Every rearrangement is finite, so this step uses no unjustified infinite
product splitting.

Crucially, pinned `Complex.tendsto_euler_sin_prod w` has the form
`πw·S_N(w) → sin(πw)`, including the leading `πw`. Apply it also to
`2w`, along the cofinal subsequence `2N`, to obtain

```text
B_N = πw·S_N(w)          → sin(πw),
A_N = π(2w)·S_(2N)(2w) → sin(2πw),
A_N = 2 B_N C_N(w)     for every N.
```

Because `sin(πw)≠0`, `B_N≠0` eventually; cancellation needs only this
eventual fact, not a claim that every finite `S_N(w)` is nonzero. Hence
`C_N(w)=A_N/(2B_N)` eventually. Continuity of division at the nonzero
limit and `sin(2πw)=2 sin(πw) cos(πw)` yield
`C_N(w)→cos(πw)`. The first theorem then changes that limit to the
exact factorial `waveSeries` value in the second theorem.

## Boundary of this gate

The sine premise excludes integer `w`, including zero. At `w=0` both
sides are directly one, but the quotient proof gives `0/0`; at other
integer `w`, it also gives `0/0`. A later lemma must extend convergence to
those values, for example by locally uniform convergence of the odd
products and continuity, as required by the broader reviewed
`COSINE_PRODUCT_PRE_REVIEW.md`. Pointwise convergence on the dense
noninteger set cannot be silently promoted to all complex `w` or all
complex `z`.

Even an all-complex product identity would still need fixed-degree
coefficient transfer to show that the infinite elementary symmetric
coefficients are exactly `1/(2j)!`, followed by the Toeplitz,
Jacobi–Trudi, tableau-tail, and normalized-existence steps. The recent
conditional `LargeOrderDisk.lean` proves the closed-disk bound only after
that denominator coefficient estimate is supplied. This dense-set lemma
is a genuine step toward that chain, not a proof of the all-order Target.
No existing proof module, frozen statement, ID registry, metadata, or CI
file is to change, and no Lean implementation begins before a separate
review of this exact contract.

## Source binding

SHA-256 at pre-review time:

| Source | SHA-256 |
| --- | --- |
| `matrix-functions-and-stability/MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| `references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `docs/lean/proofs/MF-03/ALL_ORDER_SOURCE_OBLIGATIONS.md` | `96399593ee86dedb1020da3f9d9301e865c82eec1c801917edcf587e59a58aa6` |
| `docs/lean/proofs/MF-03/COSINE_PRODUCT_PRE_REVIEW.md` | `b78f8d9255dee8ffd2a6c4add6637ce95dbeaad6c61b3e87148bb101d3091b9a` |
| `docs/lean/proofs/MF-03/COSINE_PRODUCT_INDEPENDENT_PRE_REVIEW.md` | `7cb877be8cc8c2db7f0fbde9529aa19d047020e3ea7eeaf86bc91aa9336a76a4` |
| `lean-statements/NLA/Proofs/MF03/CosineProduct.lean` | `a80cd280636110b108e0a13702a55c57d15b739cfc1e73f73bd76eb330689c8a` |
| Pinned Mathlib `EulerSineProd.lean` | `0988322f130952835b0da8d43d24b44c281af10bf149bb869ac750160ec1d5ac` |
| Pinned Mathlib trigonometric `Series.lean` | `307b22a20bcee20728e6bfda013c6f08fb126a25a2fe5e7d6cedb031bcd6a079` |

The mathematical sources are the manuscript's Euler cosine product and
factorial series, together with the pinned Euler sine-product and cosine
series theorems. Review must verify both proposed statements and the exact
leading factor, signs, parity split, and exceptional-set limitation.
