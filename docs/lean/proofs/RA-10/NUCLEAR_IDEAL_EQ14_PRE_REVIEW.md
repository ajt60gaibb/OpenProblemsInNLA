# RA-10 Equation (14): exact nuclear ideal property and selected resolvent estimate

**Status:** source-locked mathematical, indexing, norm-instance and numerical precontract for independent review. No Lean implementation or nuclear ideal theorem is claimed yet.

## Frozen source and prior exact gates

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/NuclearNormZero.lean` | `b4663cb5a4fdbfdcc5b97e515552946eda39eb62c57c65c4f539895e5ce3dc0f` |
| `lean-statements/NLA/Proofs/RA10/MatchedLeadingEq14Restricted.lean` | `fa51611236471f41313689afaf6853a7b9c8b3ad51aae5c775819802297c2dd9` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventOpNorm.lean` | `691ca03af857206b37367a0b5334080f0ae68b801e5a51d93905ec78aa2f95ff` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventOpNormSelected.lean` | `845a5cdcc7eb79f87a76e66cdb4614207b82b74f1fb8bb4137e7806a6c8a18ef` |
| Pinned Mathlib `Mathlib/Analysis/InnerProductSpace/SingularValues.lean` and `Mathlib/Analysis/CStarAlgebra/Matrix.lean` | Lean 4.33.1 and repository-locked Mathlib dependency |

The original solution's Equation (14) is calculated **on `range(P)`** for `B₀` with selected eigenvalues `a₁,…,aₖ`, actual `C=PAP`, and ridge atom `f_s(t)=t/(s+t)`. It states

```text
‖f_s(B₀)−f_s(C)‖_*
 = ‖s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹‖_*
 ≤ (1/(s+c)) ‖B₀−C‖_*,       c=a_k>0.
```

The completed exact restricted identity inserts the selected projector on both sides of the **left** resolvent:

```text
FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat
 − FunctionMatrix (ridgeAtom s) eigenvaluesC QC
= s • ((P * RB * P) * (B₀−C) * RC),
RB=(sI+B₀)⁻¹, RC=(sI+C)⁻¹.
```

Its nuclear-norm equality is already a literal congruence, not an inequality. The same supplied `QAhat` is used for `P` and `B₀`; `QC` is the independently supplied ordered basis of the **actual** C. No commutation of `B₀` and C or of the two resolvents is assumed.

## Exact norm semantics and ideal property

The frozen `NLA.Statements.RA10.NuclearNorm M` is the real sum `Σ_{i:Fin n} (Matrix.toEuclideanLin M).singularValues i.val`. It is the Schatten 1/nuclear norm of the real Euclidean linear operator, including all `n` singular values and `n=0`. Under **`open scoped Matrix.Norms.L2Operator`**, `‖M‖` is the pinned Euclidean induced operator norm: `Matrix.cstar_norm_def` identifies it with `‖Matrix.toEuclideanCLM M‖`; `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` identifies the underlying operator whose singular values define the frozen nuclear norm. These are two distinct norms on the same matrix. No entrywise, Frobenius, or default matrix norm may replace either object.

For arbitrary real square matrices X,Y and scalar r, the exact required generic facts are

```text
NuclearNorm (r • X) = |r| * NuclearNorm X,
NuclearNorm (X * Y) ≤ ‖X‖₂→₂ * NuclearNorm Y,
NuclearNorm (X * Y) ≤ NuclearNorm X * ‖Y‖₂→₂.
```

The two multiplication inequalities are the finite-dimensional nuclear ideal property, with coefficient one. They hold for nonnormal/noncommuting matrices and `n=0`. `nuclearNorm_nonneg` is already kernel-proved; no triangle inequality is needed for this Eq. (14) step. The pinned Mathlib `SingularValues.lean` visibly defines singular values and their nonnegativity/zero criteria but does **not** expose a direct nuclear ideal theorem; implementation must derive these facts in the kernel from pinned APIs or report the exact missing bridge. A proof may use a finite singular-value decomposition, rank-one decomposition plus trace duality, or another exact mathematical argument. No `sorry`, axiom, `native_decide`, numerical computation, or changed norm definition is permitted.

## Exact numerical application, factor s, and zero-based cutoff

Assume `s>0`, `1≤k<n`, source `j : Fin n` with `j.val+1=k`, and original independently supplied `hA`, `hAhat`; let `c=eigenvaluesA j=a_k` (one based). The source's positive-tail branch has `c>0`, but the following algebra and already proved operator bounds also hold when `c=0`; no extra `c>0` assumption is needed. In either case `s+c>0` because `hA` supplies `c≥0`.

Let `X=P*RB*P`, `D=B₀−C`, `Y=RC`. The existing sharp L2 operator bounds are

```text
‖X‖₂→₂ ≤ 1/(s+c),       ‖Y‖₂→₂ ≤ 1/s.
```

The left sandwich is essential: the full `RB` has complementary eigenvalue `1/s`, generally larger than `1/(s+c)`. Nuclear homogeneity and the two ideal inequalities, in the exact product order `((X*D)*Y)`, give

```text
NuclearNorm (s • (X*D*Y))
 = s * NuclearNorm ((X*D)*Y)
 ≤ s * ‖X‖₂→₂ * NuclearNorm D * ‖Y‖₂→₂
 ≤ s * (1/(s+c)) * NuclearNorm D * (1/s)
 = (1/(s+c)) * NuclearNorm D.
```

The scalar inequalities use `s>0`, `s+c>0`, `NuclearNorm D≥0`, and nonnegative operator norms. The exact factor `s` cancels the right resolvent's `1/s`; no factor of 2, n, k, or `1/s` remains. Applying the existing exact restricted nuclear equality yields the source Eq. (14) bound. Ties, zeros, arbitrary supplied QC, and noncommutation are included; `n=0` is vacuous in the final statement because `1≤k<n` is impossible, while generic ideal facts include it.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.NuclearIdealEq14` module, import the frozen Eq. (14) equality and both operator-norm gates, and explicitly `open scoped Matrix.Norms.L2Operator`. `NuclearNorm` is always the frozen definition. The generic facts may be frozen one at a time as honest stages; no Eq. (14) inequality should be stated as proved until all facts and numerical cancellation pass LeanCert kernel.

```lean
namespace NLA.Proofs.RA10

theorem nuclearNorm_smul {n : ℕ} (r : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (r • X) =
      |r| * NLA.Statements.RA10.NuclearNorm X := by
  ...

theorem nuclearNorm_mul_le_left {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      ‖X‖ * NLA.Statements.RA10.NuclearNorm Y := by
  ...

theorem nuclearNorm_mul_le_right {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) ≤
      NLA.Statements.RA10.NuclearNorm X * ‖Y‖ := by
  ...

theorem matchedLeading_ridge_nuclear_product_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (j : Fin n) (hj : j.val + 1 = k) :
    let P := selectedProjection k QAhat
    let B₀ := NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat
    let C := P * A * P
    let RB := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + B₀)⁻¹
    let RC := (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹
    NLA.Statements.RA10.NuclearNorm (s • ((P * RB * P) * (B₀ - C) * RC)) ≤
      (1 / (s + eigenvaluesA j)) * NLA.Statements.RA10.NuclearNorm (B₀ - C) := by
  ...

theorem matchedLeading_ridge_nuclear_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat eigenvaluesC : Fin n → ℝ}
    {QA QAhat QC : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition
      (selectedProjection k QAhat * A * selectedProjection k QAhat) eigenvaluesC QC)
    (j : Fin n) (hj : j.val + 1 = k) :
    NLA.Statements.RA10.NuclearNorm
      (NLA.Statements.RA10.FunctionTruncation k (ridgeAtom s) eigenvaluesA QAhat -
        NLA.Statements.RA10.FunctionMatrix (ridgeAtom s) eigenvaluesC QC) ≤
      (1 / (s + eigenvaluesA j)) *
        NLA.Statements.RA10.NuclearNorm
          (NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat -
            selectedProjection k QAhat * A * selectedProjection k QAhat) := by
  ...

end NLA.Proofs.RA10
```

## Independent review boundary

Check the pinned nuclear/operator norm distinction and singular-value cutoff, generic homogeneity and **both** coefficient-one ideal inequalities, selected left resolvent sandwich, multiplication order, actual C=PAP, zero-based `j.val+1=k`, all factors and denominator signs, and exact cancellation of s. Ensure the theorem has no premise assuming the desired inequality and no replacement of `NuclearNorm` by L2 norm. After approval, implement only kernel-proved stages, freeze source SHA, and request independent imported exact-signature/source/axiom audit. Source nuclear pinching (8), compression Lemma 2, spectral perturbation, arbitrary selected approximants, integral representation, and the full RA-10 Target remain open.
