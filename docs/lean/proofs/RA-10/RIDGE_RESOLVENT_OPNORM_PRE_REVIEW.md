# RA-10 exact Euclidean operator-norm resolvent factors

**Status:** source-locked mathematical/numerical and exact-signature precontract for independent review. No Lean implementation or proof is claimed.

## Frozen sources and pinned norm semantics

| Source | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-10/README.md` | `cbf022a051a4fd445b49fa977e1f2541e332d588b4c039a14588ce234f4eb742` |
| `randomized-and-low-rank-approximation/RA-10/solution.md` | `efdb21c8e43acebac863b49e955cc7058926f45ab5d230be31834a60c9fb679c` |
| `lean-statements/NLA/Statements/RA10.lean` | `dd7235bc531fd808d7eb5c591b42c618fe8eba1104af4d54c981742d77d22c82` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventLoewner.lean` | `c06a186419efdc23cf27a63238134becc4f89e215649daa67b459bd72b159d06` |
| `lean-statements/NLA/Proofs/RA10/RidgeResolventLoewnerSelected.lean` | `82ca6ccb9434dc4d57737c4d421be929df6bf06bdbb42f74e7b260aa2e3f9186` |
| Pinned Mathlib `Mathlib/Analysis/CStarAlgebra/Matrix.lean` | Pin: Lean 4.33.1 and the repository's locked Mathlib dependency |

The pinned Mathlib file defines a **scoped** `Matrix.Norms.L2Operator` norm instance. Under `open scoped Matrix.Norms.L2Operator`, its `Matrix.cstar_norm_def` gives `‖M‖=‖Matrix.toEuclideanCLM M‖`, the Euclidean continuous-linear-map operator norm. `Matrix.coe_toEuclideanCLM_eq_toEuclideanLin` identifies the underlying linear map with the `Matrix.toEuclideanLin M` whose singular values define frozen `NLA.Statements.RA10.NuclearNorm`. These are distinct norms on the **same** matrix/operator; this gate does not redefine or replace `NuclearNorm`. Mathlib's `Matrix.l2_opNorm_mul` and `Matrix.l2_opNorm_diagonal` are available in the same pinned module.

## Exact source mathematics

Source Equation (14) uses the product `s(sI+B₀)⁻¹(B₀−C)(sI+C)⁻¹` and says its factors, **restricted to** `range(P)`, have operator norms at most `1/(s+c)` and `1/s`. The already reviewed Loewner gate proves their PSD counterparts with the same constants. This gate proves the following actual Euclidean operator-norm bounds, preserving exact denominators:

1. For all `n`, `s>0`, and every supplied ordered PSD decomposition of `C`,

   ```text
   ‖(sI+C)⁻¹‖₂→₂ ≤ 1/s.
   ```

   This includes singular `C`, zero/tied eigenvalues and `n=0`. The inverse is the same actual matrix inverse as in the frozen ridge resolvent gates. Its spectral coefficients are `1/(s+c_i)` with `0≤1/(s+c_i)≤1/s`.

2. Retain `A,eigenvaluesA,QA` and `Ahat,eigenvaluesAhat,QAhat` independently supplied. Put `B₀=FunctionTruncation k id eigenvaluesA QAhat` and `P=selectedProjection k QAhat`. In the frozen target range `1≤k<n`, take `j : Fin n` satisfying `j.val+1=k`; exactly `c=eigenvaluesA j=a_k` in source one-based indexing. Then

   ```text
   ‖P(sI+B₀)⁻¹P‖₂→₂ ≤ 1/(s+c).
   ```

   The sandwich by `P` is essential: on the complement, `B₀=0` and the **full** inverse has eigenvalue `1/s`, which can exceed `1/(s+c)`. On selected coordinates the coefficients are `1/(s+a_i)≤1/(s+c)` by antitonicity. Ties give equality; `c=0` is allowed. The theorem does not assume `QA=QAhat`, `B₀` and `C` commute, or any spectral gap. The empty selected case is outside the frozen `1≤k<n` domain; the full-matrix theorem handles `n=0`.

The source's claimed Equation (14) nuclear inequality still needs exact support/commutation algebra on `range(P)` and a **new** nuclear ideal-property theorem for frozen `NuclearNorm`; the pinned `SingularValues.lean` provides no such triangle/ideal theorem. Neither operator-norm bound alone is presented as that inequality.

## Proposed exact Lean declarations

Use a new `NLA.Proofs.RA10.RidgeResolventOpNorm` module, importing the frozen statement, the approved Loewner modules and `Mathlib.Analysis.CStarAlgebra.Matrix`. In that module explicitly write `open scoped Matrix.Norms.L2Operator` so `‖M‖` is the pinned Euclidean operator norm, not an entrywise or Frobenius norm. The declarations are:

```lean
namespace NLA.Proofs.RA10

theorem spectralShift_resolvent_opNorm_le {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {C : Matrix (Fin n) (Fin n) ℝ} {eigenvaluesC : Fin n → ℝ}
    {QC : Matrix (Fin n) (Fin n) ℝ}
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    ‖(s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹‖ ≤ 1 / s := by
  ...

theorem matchedLeading_selectedResolvent_opNorm_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    ‖selectedProjection k QAhat *
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
      selectedProjection k QAhat‖ ≤ 1 / (s + eigenvaluesA j) := by
  ...

end NLA.Proofs.RA10
```

Proof may use the exact spectral diagonalization already derived from the supplied bases, or a proved bridge from frozen `PositiveSemidefinite` interval bounds to the pinned L2 operator norm. It must use the scoped norm instance explicitly and discharge the orthonormal change-of-basis bound, including `n=0`; no default matrix norm coercion is allowed.

## Review and verification

Independent review must check norm semantics, both sharp source constants, necessity of the selected sandwich, the zero-based cutoff, all zero/tie/empty cases and the absence of a nuclear-norm conclusion. Implement only after approval; direct pinned Lean 4.33.1/LeanCert kernel checks and frozen-source imported exact-signature/axiom audit then apply. The nuclear ideal property, Equation (14) inequality, min-max/spectral perturbation bounds, ridge compression Lemma 2, operator-monotone integral representation and full RA-10 `Target` remain open.
