import NLA.Proofs.RA10.NuclearIdealOperatorBridge
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Ring

/-! RA-10: the sharp Euclidean operator-norm Gram order. This is one
coefficient-one dependency for the frozen nuclear ideal inequality; that
inequality and the final Target remain open. -/

set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

private theorem gram_quadratic_eq_sum_sq {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * (M.transpose * M) i j * x j) =
      ∑ i : Fin n, ((M *ᵥ x) i) ^ 2 := by
  calc
    (∑ i : Fin n, ∑ j : Fin n,
      x i * (M.transpose * M) i j * x j) =
        x ⬝ᵥ ((M.transpose * M) *ᵥ x) := by
      rw [Matrix.dot_mulVec_eq_sum_sum]
      exact Finset.sum_comm
    _ = x ⬝ᵥ (M.transpose *ᵥ (M *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec]
    _ = (x ᵥ* M.transpose) ⬝ᵥ (M *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec]
    _ = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
      rw [Matrix.vecMul_transpose]
    _ = ∑ i : Fin n, ((M *ᵥ x) i) ^ 2 := by
      simp [dotProduct, pow_two]

private theorem gram_difference_quadratic {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n,
      x i * ((‖X‖ ^ 2) • (Y.transpose * Y) -
        (X * Y).transpose * (X * Y)) i j * x j) =
      ‖X‖ ^ 2 * (∑ i : Fin n, ((Y *ᵥ x) i) ^ 2) -
        ∑ i : Fin n, (((X * Y) *ᵥ x) i) ^ 2 := by
  have hentry (i j : Fin n) :
      x i * ((‖X‖ ^ 2) • (Y.transpose * Y) -
        (X * Y).transpose * (X * Y)) i j * x j =
      ‖X‖ ^ 2 * (x i * (Y.transpose * Y) i j * x j) -
        x i * ((X * Y).transpose * (X * Y)) i j * x j := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  simp_rw [hentry, Finset.sum_sub_distrib, ← Finset.mul_sum,
    gram_quadratic_eq_sum_sq]

theorem nuclearIdeal_left_gram_order {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.PositiveSemidefinite
      ((‖X‖ ^ 2) • (Y.transpose * Y) -
        (X * Y).transpose * (X * Y)) := by
  constructor
  · intro i j
    have hsym :
        (((‖X‖ ^ 2) • (Y.transpose * Y) -
          (X * Y).transpose * (X * Y)).transpose) =
          ((‖X‖ ^ 2) • (Y.transpose * Y) -
            (X * Y).transpose * (X * Y)) := by
      simp [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul]
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hsym
    simpa [Matrix.transpose_apply] using hij.symm
  · intro x
    let v : EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm (Y *ᵥ x)
    let w : EuclideanSpace ℝ (Fin n) :=
      (EuclideanSpace.equiv (Fin n) ℝ).symm ((X * Y) *ᵥ x)
    have hop : ‖w‖ ≤ ‖X‖ * ‖v‖ := by
      have h := Matrix.l2_opNorm_mulVec X v
      simpa [v, w, Matrix.mulVec_mulVec] using h
    have hsq : ‖w‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖v‖ ^ 2 := by
      have hn : 0 ≤ ‖X‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
      nlinarith [mul_nonneg (sub_nonneg.mpr hop)
        (add_nonneg hn (norm_nonneg w))]
    have hv : ‖v‖ ^ 2 = ∑ i : Fin n, ((Y *ᵥ x) i) ^ 2 := by
      simpa [v] using EuclideanSpace.real_norm_sq_eq v
    have hw : ‖w‖ ^ 2 = ∑ i : Fin n, (((X * Y) *ᵥ x) i) ^ 2 := by
      simpa [w] using EuclideanSpace.real_norm_sq_eq w
    rw [gram_difference_quadratic, ← hv, ← hw]
    exact sub_nonneg.mpr hsq

#assert_trust kernel gram_quadratic_eq_sum_sq
#assert_trust kernel gram_difference_quadratic
#assert_trust kernel nuclearIdeal_left_gram_order
#print axioms nuclearIdeal_left_gram_order

end NLA.Proofs.RA10
