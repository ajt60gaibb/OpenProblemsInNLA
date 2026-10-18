import NLA.Proofs.PF05.Congruence
import Mathlib.Tactic

/-! The actual congruence equivalence relation and transport of frozen
straight-line rigidity. All inverses retain nonzero determinant guards. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05
noncomputable section

variable {p q : ℕ}

/-- The precise existential relation in the frozen uniqueness predicate. -/
def Congruent (A At : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B Bt : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S.det ≠ 0 ∧
    (∀ i, At i = primalCongruence S (A i)) ∧
    (∀ j, Bt j = dualCongruence S (B j))

theorem primalCongruence_comp (S T A : Matrix (Fin 2) (Fin 2) ℝ) :
    primalCongruence T (primalCongruence S A) = primalCongruence (S * T) A := by
  simp [primalCongruence, Matrix.transpose_mul, Matrix.mul_assoc]

theorem dualCongruence_comp (S T B : Matrix (Fin 2) (Fin 2) ℝ) :
    dualCongruence T (dualCongruence S B) = dualCongruence (S * T) B := by
  simp [dualCongruence, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.mul_assoc]

theorem congruence_inv_det_ne_zero (S : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.det ≠ 0) : S⁻¹.det ≠ 0 := by
  rw [Matrix.det_nonsing_inv]
  simpa only [Ring.inverse_eq_inv] using inv_ne_zero hS

@[simp] theorem primalCongruence_one (A : Matrix (Fin 2) (Fin 2) ℝ) :
    primalCongruence 1 A = A := by simp [primalCongruence]
@[simp] theorem dualCongruence_one (B : Matrix (Fin 2) (Fin 2) ℝ) :
    dualCongruence 1 B = B := by simp [dualCongruence]

theorem primalCongruence_cancel_left (S A : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.det ≠ 0) : primalCongruence S⁻¹ (primalCongruence S A) = A := by
  rw [primalCongruence_comp, S.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hS), primalCongruence_one]
theorem primalCongruence_cancel_right (S A : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.det ≠ 0) : primalCongruence S (primalCongruence S⁻¹ A) = A := by
  rw [primalCongruence_comp, S.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hS), primalCongruence_one]
theorem dualCongruence_cancel_left (S B : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.det ≠ 0) : dualCongruence S⁻¹ (dualCongruence S B) = B := by
  rw [dualCongruence_comp, S.mul_nonsing_inv (isUnit_iff_ne_zero.mpr hS), dualCongruence_one]
theorem dualCongruence_cancel_right (S B : Matrix (Fin 2) (Fin 2) ℝ)
    (hS : S.det ≠ 0) : dualCongruence S (dualCongruence S⁻¹ B) = B := by
  rw [dualCongruence_comp, S.nonsing_inv_mul (isUnit_iff_ne_zero.mpr hS), dualCongruence_one]

theorem congruent_refl (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ) : Congruent A A B B := by
  exact ⟨1, by simp, by simp, by simp⟩

theorem congruent_trans {A At Au : Fin p → Matrix (Fin 2) (Fin 2) ℝ}
    {B Bt Bu : Fin q → Matrix (Fin 2) (Fin 2) ℝ}
    (h : Congruent A At B Bt) (h' : Congruent At Au Bt Bu) : Congruent A Au B Bu := by
  obtain ⟨S, hS, hA, hB⟩ := h
  obtain ⟨T, hT, hAt, hBt⟩ := h'
  refine ⟨S * T, by rw [Matrix.det_mul]; exact mul_ne_zero hS hT, ?_, ?_⟩
  · intro i
    rw [hAt, hA, primalCongruence_comp]
  · intro j
    rw [hBt, hB, dualCongruence_comp]

theorem congruent_symm {A At : Fin p → Matrix (Fin 2) (Fin 2) ℝ}
    {B Bt : Fin q → Matrix (Fin 2) (Fin 2) ℝ}
    (h : Congruent A At B Bt) : Congruent At A Bt B := by
  obtain ⟨S, hS, hA, hB⟩ := h
  refine ⟨S⁻¹, congruence_inv_det_ne_zero S hS, ?_, ?_⟩
  · intro i
    rw [hA, primalCongruence_cancel_left S _ hS]
  · intro j
    rw [hB, dualCongruence_cancel_left S _ hS]

theorem infinitesimallyRigid_congruence
    (A : Fin p → Matrix (Fin 2) (Fin 2) ℝ)
    (B : Fin q → Matrix (Fin 2) (Fin 2) ℝ)
    (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.det ≠ 0)
    (h : InfinitesimallyRigid A B) :
    InfinitesimallyRigid (fun i => primalCongruence S (A i))
      (fun j => dualCongruence S (B j)) := by
  intro E F hEF
  have hback := feasibleDirection_congruence _ E _ F hEF S⁻¹ (congruence_inv_det_ne_zero S hS)
  simp only [primalCongruence_cancel_left S _ hS, dualCongruence_cancel_left S _ hS] at hback
  obtain ⟨d, hdA, hdB⟩ := h _ _ hback
  refine ⟨d, ?_, ?_⟩
  · intro i
    have he := congrArg (primalCongruence S) (hdA i)
    rw [primalCongruence_cancel_right S _ hS] at he
    simpa [primalCongruence] using he
  · intro j
    have he := congrArg (dualCongruence S) (hdB j)
    rw [dualCongruence_cancel_right S _ hS] at he
    simpa [dualCongruence] using he

#assert_trust kernel primalCongruence_comp
#assert_trust kernel dualCongruence_comp
#assert_trust kernel congruent_symm
#assert_trust kernel congruent_trans
#assert_trust kernel infinitesimallyRigid_congruence
#print axioms congruent_trans
#print axioms infinitesimallyRigid_congruence
end
end NLA.Proofs.PF05
