/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-26.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI26.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI26

theorem admissibleFunction_iff_proved (f : ℝ → ℝ) :
    AdmissibleFunction f ↔
      (0 ≤ f 0 ∧ ∀ x y θ : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ θ → θ ≤ 1 →
        θ * f x + (1 - θ) * f y ≤ f (θ * x + (1 - θ) * y)) := by
  constructor
  · intro hf
    refine ⟨hf.2, ?_⟩
    intro x y θ hx hy hθ hθ1
    simpa only [smul_eq_mul] using
      hf.1.2 hx hy hθ (sub_nonneg.mpr hθ1) (by ring : θ + (1 - θ) = 1)
  · rintro ⟨h0, hf⟩
    refine ⟨⟨convex_Ici (0 : ℝ), ?_⟩, h0⟩
    intro x hx y hy a b ha hb hab
    have hb' : b = 1 - a := by linarith
    simpa only [smul_eq_mul, hb'] using hf x y a hx hy ha (by linarith)

/-- Every bare function on the finite spectrum has the true spectral CFC value. -/
theorem functionalCalculus_eq_spectral_proved {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    functionalCalculus f A =
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  simpa only [functionalCalculus, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Function.comp_def, star_eq_conjTranspose] using! hA.cfc_eq f

theorem functionalCalculus_congr_nonneg_proved {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (f g : ℝ → ℝ) (hfg : Set.EqOn f g (Set.Ici 0)) :
    functionalCalculus f A = functionalCalculus g A := by
  rw [functionalCalculus_eq_spectral_proved A hA.isHermitian f,
    functionalCalculus_eq_spectral_proved A hA.isHermitian g]
  apply congrArg (fun D : Matrix (Fin n) (Fin n) ℂ =>
    (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) * D *
      (hA.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose)
  apply congrArg Matrix.diagonal
  funext i
  rw [hfg (hA.eigenvalues_nonneg i)]

theorem quadratic_cfc_proved {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    functionalCalculus witnessFunction A = A - A ^ 2 := by
  unfold functionalCalculus witnessFunction
  rw [cfc_sub (p := IsSelfAdjoint) (fun x : ℝ => x) (fun x => x ^ 2) A,
    cfc_pow (p := IsSelfAdjoint) (fun x : ℝ => x) 2 A (by fun_prop) hA.isSelfAdjoint,
    cfc_id' ℝ A hA.isSelfAdjoint]

/-- The exact Jensen gap proves concavity for all real arguments and all allowed weights. -/
lemma witness_function_admissible : AdmissibleFunction witnessFunction := by
  apply (admissibleFunction_iff_proved witnessFunction).mpr
  refine ⟨by norm_num [witnessFunction], ?_⟩
  intro x y θ _ _ hθ hθ1
  apply sub_nonneg.mp
  calc
    0 ≤ θ * (1 - θ) * (x - y) ^ 2 :=
      mul_nonneg (mul_nonneg hθ (sub_nonneg.mpr hθ1)) (sq_nonneg (x - y))
    _ = witnessFunction (θ * x + (1 - θ) * y) -
        (θ * witnessFunction x + (1 - θ) * witnessFunction y) := by
      unfold witnessFunction
      ring

lemma witnessP_posSemidef : witnessP.PosSemidef := by
  let v : Fin 2 → ℂ := ![1, 0]
  have h : witnessP = Matrix.vecMulVec v (star v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessP, v, Matrix.vecMulVec]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star v

lemma witnessQ_posSemidef : witnessQ.PosSemidef := by
  let v : Fin 2 → ℂ := ![3 / 5, 4 / 5]
  have h : witnessQ = Matrix.vecMulVec v (star v) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessQ, v, Matrix.vecMulVec, map_ofNat]
  rw [h]
  exact Matrix.posSemidef_vecMulVec_self_star v

lemma witnessP_squared : witnessP ^ 2 = witnessP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessP, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma witnessQ_squared : witnessQ ^ 2 = witnessQ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessQ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma witness_image_P : functionalCalculus witnessFunction witnessP = 0 := by
  rw [quadratic_cfc_proved _ witnessP_posSemidef.isHermitian, witnessP_squared, sub_self]

lemma witness_image_Q : functionalCalculus witnessFunction witnessQ = 0 := by
  rw [quadratic_cfc_proved _ witnessQ_posSemidef.isHermitian, witnessQ_squared, sub_self]

lemma witness_image_sum :
    functionalCalculus witnessFunction (witnessP + witnessQ) = witnessImage := by
  rw [quadratic_cfc_proved _ (witnessP_posSemidef.add witnessQ_posSemidef).isHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessP, witnessQ, witnessImage, pow_two, Matrix.mul_apply,
      Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_two]

lemma witness_vector_ne_zero : witnessVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [witnessVector] at h0

lemma witness_quadratic :
    star witnessVector ⬝ᵥ (witnessImage *ᵥ witnessVector) = (6 / 5 : ℂ) := by
  norm_num [witnessVector, witnessImage, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    map_ofNat]

/-- The only interval computation is this point certificate. It is retained
explicitly in the final all-unitary contradiction. -/
lemma witness_positive : (0 : ℝ) < 6 / 5 := by
  interval_decide (trust := kernel)

theorem witness_data_proved :
    AdmissibleFunction witnessFunction ∧
    witnessFunction 0 = 0 ∧ witnessFunction 2 = -2 ∧
    witnessP.PosSemidef ∧ witnessQ.PosSemidef ∧
    witnessP ^ 2 = witnessP ∧ witnessQ ^ 2 = witnessQ ∧
    functionalCalculus witnessFunction witnessP = 0 ∧
    functionalCalculus witnessFunction witnessQ = 0 ∧
    functionalCalculus witnessFunction (witnessP + witnessQ) = witnessImage ∧
    witnessVector ≠ 0 ∧
    star witnessVector ⬝ᵥ (witnessImage *ᵥ witnessVector) = (6 / 5 : ℂ) ∧
    (0 : ℝ) < 6 / 5 := by
  exact ⟨witness_function_admissible, by norm_num [witnessFunction],
    by norm_num [witnessFunction], witnessP_posSemidef, witnessQ_posSemidef,
    witnessP_squared, witnessQ_squared, witness_image_P, witness_image_Q,
    witness_image_sum, witness_vector_ne_zero, witness_quadratic, witness_positive⟩

theorem counterexample_proved (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ¬ (functionalCalculus witnessFunction (witnessP + witnessQ) ≤
      unitaryConjugate U (functionalCalculus witnessFunction witnessP) +
        unitaryConjugate V (functionalCalculus witnessFunction witnessQ)) := by
  intro h
  rw [witness_image_sum, witness_image_P, witness_image_Q] at h
  simp only [unitaryConjugate, mul_zero, zero_mul, add_zero, Matrix.le_iff,
    zero_sub] at h
  have hq := h.dotProduct_mulVec_nonneg witnessVector
  rw [Matrix.neg_mulVec, dotProduct_neg, witness_quadratic] at hq
  have hr := (Complex.nonneg_iff.mp hq).1
  have heq : (-(6 / 5 : ℂ)).re = -(6 / 5 : ℝ) := by norm_num
  rw [heq] at hr
  exact (not_le_of_gt (neg_neg_of_pos witness_positive)) hr

theorem not_subadditivityConjecture_proved : ¬ SubadditivityConjecture := by
  intro h
  obtain ⟨U, V, hUV⟩ := h 2 (by decide) witnessP witnessQ
    witnessP_posSemidef witnessQ_posSemidef witnessFunction witness_function_admissible
  exact counterexample_proved U V hUV

#assert_trust kernel admissibleFunction_iff_proved
#assert_trust kernel functionalCalculus_eq_spectral_proved
#assert_trust kernel functionalCalculus_congr_nonneg_proved
#assert_trust kernel quadratic_cfc_proved
#assert_trust kernel witness_positive
#assert_trust kernel witness_data_proved
#assert_trust kernel counterexample_proved
#assert_trust kernel not_subadditivityConjecture_proved

#print axioms admissibleFunction_iff_proved
#print axioms functionalCalculus_eq_spectral_proved
#print axioms functionalCalculus_congr_nonneg_proved
#print axioms quadratic_cfc_proved
#print axioms witness_positive
#print axioms witness_data_proved
#print axioms counterexample_proved
#print axioms not_subadditivityConjecture_proved

end NLA.MI26
