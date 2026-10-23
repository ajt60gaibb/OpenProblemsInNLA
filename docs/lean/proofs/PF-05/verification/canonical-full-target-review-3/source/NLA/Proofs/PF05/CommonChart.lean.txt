import NLA.Proofs.PF05.Congruence
import NLA.Proofs.PF05.ZeroPair
import Mathlib.Algebra.Polynomial.Roots

/-! One actual determinant-one shear puts both finite nonzero PSD families in
one affine contact chart. No positive-definiteness assumption is used. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.PF05.CommonChart
open NLA.Statements.PF05
open Polynomial
open scoped BigOperators Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The same lower shear acts on the primal and weighted-dual sides. -/
def lowerShear (z : ℝ) : M2 := !![1,0;z,1]

theorem lowerShear_det (z : ℝ) : (lowerShear z).det = 1 := by
  simp [lowerShear, Matrix.det_fin_two]

theorem lowerShear_inv (z : ℝ) : (lowerShear z)⁻¹ = lowerShear (-z) := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowerShear, Matrix.mul_apply, Fin.sum_univ_two]

def primalQuadratic (A : M2) : ℝ[X] :=
  C (A 0 0) + C (2*A 0 1)*X + C (A 1 1)*X^2

def dualQuadratic (B : M2) : ℝ[X] :=
  C (B 1 1) + C (-2*B 0 1)*X + C (B 0 0)*X^2

theorem primalQuadratic_ne_zero (A : M2)
    (hA : PositiveSemidefinite A) (hne : A ≠ 0) : primalQuadratic A ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hz
  norm_num [primalQuadratic] at h0 h2
  obtain h | h := nonzero_psd_two_positive_diagonal A hA hne <;> linarith

theorem dualQuadratic_ne_zero (B : M2)
    (hB : PositiveSemidefinite B) (hne : B ≠ 0) : dualQuadratic B ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hz
  norm_num [dualQuadratic] at h0 h2
  obtain h | h := nonzero_psd_two_positive_diagonal B hB hne <;> linarith

theorem primal_lowerShear_entry (z : ℝ) (A : M2) (hs : Symmetric A) :
    primalCongruence (lowerShear z) A 0 0 = (primalQuadratic A).eval z := by
  simp [primalCongruence, lowerShear, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, primalQuadratic, hs 1 0]
  ring

theorem dual_lowerShear_entry (z : ℝ) (B : M2) (hs : Symmetric B) :
    dualCongruence (lowerShear z) B 1 1 = (dualQuadratic B).eval z := by
  rw [dualCongruence, lowerShear_inv]
  simp [lowerShear, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.transpose_apply, Matrix.vecMul, dotProduct, dualQuadratic, hs 1 0]
  ring

/-- A finite family of nonzero real polynomials has a common nonroot. -/
theorem exists_common_nonroot {ι : Type*} [Fintype ι]
    (P : ι → ℝ[X]) (hP : ∀ i, P i ≠ 0) :
    ∃ z : ℝ, ∀ i, (P i).eval z ≠ 0 := by
  classical
  have hprod : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hP i)
  have hex : ∃ z : ℝ, (∏ i, P i).eval z ≠ 0 := by
    by_contra! h
    apply hprod
    apply Polynomial.funext
    intro z
    simpa using h z
  obtain ⟨z,hz⟩ := hex
  refine ⟨z,?_⟩
  have hp : (∏ i, (P i).eval z) ≠ 0 := by simpa only [Polynomial.eval_prod] using hz
  exact fun i => Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)

/-- All primal 00 and dual 11 entries are strictly positive in one actual
common chart. Empty families and singular nonzero PSD factors are included. -/
theorem exists_common_lower_shear {p q : ℕ}
    (A : Fin p → M2) (B : Fin q → M2)
    (hA : ∀ i, PositiveSemidefinite (A i))
    (hB : ∀ j, PositiveSemidefinite (B j))
    (hneA : ∀ i, A i ≠ 0) (hneB : ∀ j, B j ≠ 0) :
    ∃ z : ℝ,
      (∀ i, 0 < primalCongruence (lowerShear z) (A i) 0 0) ∧
      (∀ j, 0 < dualCongruence (lowerShear z) (B j) 1 1) := by
  classical
  let P : Fin p ⊕ Fin q → ℝ[X] :=
    Sum.elim (fun i => primalQuadratic (A i)) (fun j => dualQuadratic (B j))
  have hP : ∀ k, P k ≠ 0 := by
    intro k
    cases k with
    | inl i => exact primalQuadratic_ne_zero (A i) (hA i) (hneA i)
    | inr j => exact dualQuadratic_ne_zero (B j) (hB j) (hneB j)
  obtain ⟨z,hz⟩ := exists_common_nonroot P hP
  refine ⟨z,?_,?_⟩
  · intro i
    have hnonzero : primalCongruence (lowerShear z) (A i) 0 0 ≠ 0 := by
      rw [primal_lowerShear_entry z (A i) (hA i).1]
      exact hz (Sum.inl i)
    exact lt_of_le_of_ne (psd_diag_nonneg _ (primalCongruence_psd _ _ (hA i)) 0)
      (Ne.symm hnonzero)
  · intro j
    have hnonzero : dualCongruence (lowerShear z) (B j) 1 1 ≠ 0 := by
      rw [dual_lowerShear_entry z (B j) (hB j).1]
      exact hz (Sum.inr j)
    exact lt_of_le_of_ne (psd_diag_nonneg _ (dualCongruence_psd _ _ (hB j)) 1)
      (Ne.symm hnonzero)

/-- An invertible real matrix realizing the common chart. -/
theorem exists_common_chart {p q : ℕ}
    (A : Fin p → M2) (B : Fin q → M2)
    (hA : ∀ i, PositiveSemidefinite (A i))
    (hB : ∀ j, PositiveSemidefinite (B j))
    (hneA : ∀ i, A i ≠ 0) (hneB : ∀ j, B j ≠ 0) :
    ∃ S : M2, S.det ≠ 0 ∧
      (∀ i, 0 < primalCongruence S (A i) 0 0) ∧
      (∀ j, 0 < dualCongruence S (B j) 1 1) := by
  obtain ⟨z,ha,hb⟩ := exists_common_lower_shear A B hA hB hneA hneB
  exact ⟨lowerShear z,by rw [lowerShear_det]; norm_num,ha,hb⟩

#assert_trust kernel lowerShear_det
#assert_trust kernel lowerShear_inv
#assert_trust kernel primalQuadratic_ne_zero
#assert_trust kernel dualQuadratic_ne_zero
#assert_trust kernel primal_lowerShear_entry
#assert_trust kernel dual_lowerShear_entry
#assert_trust kernel exists_common_nonroot
#assert_trust kernel exists_common_lower_shear
#assert_trust kernel exists_common_chart
#print axioms lowerShear_det
#print axioms lowerShear_inv
#print axioms primalQuadratic_ne_zero
#print axioms dualQuadratic_ne_zero
#print axioms primal_lowerShear_entry
#print axioms dual_lowerShear_entry
#print axioms exists_common_nonroot
#print axioms exists_common_lower_shear
#print axioms exists_common_chart
end NLA.Proofs.PF05.CommonChart
