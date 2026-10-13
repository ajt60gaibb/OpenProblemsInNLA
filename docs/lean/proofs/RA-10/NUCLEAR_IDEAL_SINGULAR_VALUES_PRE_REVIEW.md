# RA-10 Gram spectra and sharp left nuclear ideal: exact precontract

**Status:** source-locked mathematical, indexing, norm, and numerical precontract for independent review. No Lean implementation or final RA-10 Target proof is claimed. Implement separate staged modules only after independent approval. The Gram-order source listed below has passed its independent imported kernel audit and is committed.

## Immutable source and pinned-library locks

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/NuclearIdealGramOrder.lean` | `9f970cddf1fb1de6f5e9790b1f9f404bd70e146a75711d67e1735d72aab3c493` |
| `lean-statements/NLA/Proofs/RA10/OrderedPSDLoewnerEigenvalue.lean` | `66a356e2ebc291b2d0c7b272ad770041414e1b2a66330acf46f23f1bdbe0fc73` |
| `lean-statements/NLA/Proofs/RA10/SelectedCompressionOrderedSpectral.lean` | `d4ac007b8f7dbd53c1e107bd99a76ee30dbc70f189fea28fc71f91545fab0504` |
| `lean-statements/NLA/Proofs/RA10/CustomPSDMathlibBridge.lean` | `ca0e97485f3538275f12006d3619687d4c49bf0c1e7a8e2f698dadf87b64e0b7` |
| pinned Mathlib `Analysis/InnerProductSpace/SingularValues.lean` | `ce8193fcd5d226845a71f66b8ca7ad385358916a6e0e688745410ac412ed5c81` |
| pinned Mathlib `Analysis/InnerProductSpace/Spectrum.lean` | `f12ef613416053c759ef30179147744c64eeec90f7467644cb30e64d532d7aa6` |
| pinned Mathlib `Analysis/Matrix/Spectrum.lean` | `1ad47effa0a5fbc373ebb6cf52a6b85a66b25d3c5a86394f3dd5932ffbfc3afe` |
| pinned Mathlib `Analysis/InnerProductSpace/Adjoint.lean` | `f28b5896638f712605265a69ffe4469f1f42e1b78b10ade0844738aeecd2b2a2` |
| pinned Mathlib `Analysis/Normed/Lp/Matrix.lean` | `976400e4430cbe64214a24e37f3f98c807c30f1c9926c8cbd367ae2fd111e2f9` |

## Frozen objects and the exact numerical claim

Under `open scoped Matrix.Norms.L2Operator`, `‖X‖` is **the Euclidean induced operator norm** of the real matrix `X`, not the nuclear norm. The frozen `NLA.Statements.RA10.NuclearNorm M` is **all** `n` zero-based singular values of `Matrix.toEuclideanLin M` summed over `Fin n`. For arbitrary `n : ℕ` and real square `X,Y : Matrix (Fin n) (Fin n) ℝ`, prove with coefficient **one**:

```text
∀ i : Fin n, singularValues(toEuclideanLin (X*Y), i.val)
       ≤ ‖X‖₂→₂ * singularValues(toEuclideanLin Y, i.val),
NuclearNorm (X*Y) ≤ ‖X‖₂→₂ * NuclearNorm Y.
```

No rank, dimension, invertibility, spectral-gap, positivity-of-eigenvalue, or commutativity assumption is added. `n=0` gives empty quantification and zero sums; zero singular values and ties remain included. The target uses `X*Y`, with `X` on the **left**; this is the left ideal inequality required for the exact product order in source Eq. (14). A separate right ideal inequality is still needed there.

## Required Gram-to-singular bridge

Let `G=YᵀY` and `H=(XY)ᵀ(XY)`. Both are PSD in the frozen predicate, including `Fin 0`. For **any supplied** `OrderedPSDSpectralDecomposition G g QG`, prove the same-index equality

```text
g i = singularValues(toEuclideanLin Y, i.val)^2  (i : Fin n).
```

The index is `i.val : ℕ`, exactly the index used in frozen `NuclearNorm`, not a changed sorting/permutation or only a multiset equality. The pinned `LinearMap.sq_singularValues_fin` gives the ordered eigenvalues of `(toEuclideanLin Y).adjoint ∘ₗ toEuclideanLin Y`. The pinned matrix adjoint and multiplication identities identify that operator with `toEuclideanLin (YᵀY)`; real conjugate transpose is transpose. The pinned `Matrix.IsHermitian.eigenvalues₀` uses the **same descending `Fin n` order** after the explicit cardinality cast used in `SelectedCompressionOrderedSpectral`. Its original `eigenvalues` on `Fin n` need not itself preserve that order, so use the existing `sortedHermitianIndex n`, or compare arbitrary ordered decompositions in both directions using the audited ordered Loewner theorem and the PSD zero difference. Ties cause equal values at the affected indices; `n=0` is vacuous. If the operator and matrix eigenvalue definitions are not definitionally equal, prove equality from their common operator or charpoly, and keep the exact cast explicit. No appeal to an unsorted eigenvalue list may establish this indexed equality.

## Gram Loewner comparison and nonnegative square roots

The frozen Gram-order theorem proves exactly

```text
PositiveSemidefinite ((‖X‖₂→₂²) • G − H).
```

Choose actual ordered PSD decompositions of `G` and `H` using the existing Mathlib-to-frozen witness theorem. Since `0≤‖X‖²`, scalar multiplication of the decomposition of `G` yields an exact decomposition of `(‖X‖²)•G` with values `i↦‖X‖²*g i` and the **same** orthonormal basis. The existing ordered PSD Loewner theorem then yields `h i≤‖X‖²*g i` at each `i`. Substitute the two Gram-to-singular identities to obtain

```text
singularValues(toEuclideanLin (X*Y), i.val)^2
  ≤ ‖X‖₂→₂² * singularValues(toEuclideanLin Y, i.val)^2.
```

All singular values and `‖X‖` are nonnegative. Taking nonnegative square roots gives the coefficient-one pointwise inequality, including `‖X‖=0` and zero singular values. Sum over **every** `i:Fin n` and pull out the constant nonnegative real scalar to obtain the frozen nuclear ideal statement; no truncation or dimension factor is allowed. This reasoning does not infer the false general matrix Loewner inequality `(XY)ᵀ(XY)≤XᵀX`.

## Proposed staged exact public declarations

```lean
namespace NLA.Proofs.RA10

theorem orderedPSD_gram_eigenvalue_eq_singular_sq {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) ℝ)
    {g : Fin n → ℝ} {QG : Matrix (Fin n) (Fin n) ℝ}
    (hG : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (Y.transpose * Y) g QG) (i : Fin n) :
    g i = (Matrix.toEuclideanLin Y).singularValues i.val ^ 2 := by
  ...

end NLA.Proofs.RA10
```

```lean
open scoped Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem singularValues_left_mul_le {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    (Matrix.toEuclideanLin (X * Y)).singularValues i.val ≤
      ‖X‖ * (Matrix.toEuclideanLin Y).singularValues i.val := by
  ...

theorem nuclearIdeal_left {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      ‖X‖ * NLA.Statements.RA10.NuclearNorm Y := by
  ...

end NLA.Proofs.RA10
```

An exact scaled-decomposition helper may be public in a separate reviewed stage if needed; its signature must be submitted before implementation. Prove and freeze the Gram-index bridge first, then the pointwise inequality, then the summed ideal theorem, with independent imported exact-signature audits after each stage. Do not claim the Eq. (14) nuclear bound or final `Target` from these left-sided gates alone.

## Review gate

Independent review must check the Matrix `L2Operator` scope, all-`Fin n` singular-value semantics, zero-based matching, sorted matrix/operator eigenvalues and cardinality cast, scalar decomposition with coefficient one, Gram subtraction direction, matrix multiplication order, nonnegative-square-root step, ties/zeros/`Fin 0`, and the exact declared signatures. No Lean implementation before approval; require direct pinned LeanCert kernel checks and separate imported exact-signature/source/axiom audit after implementation. No `sorry`, `admit`, custom axiom, `native_decide`, or unsafe declaration.
