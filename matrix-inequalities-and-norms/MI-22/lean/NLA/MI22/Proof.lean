/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Complete refutation of MI-22, using the explicitly disclosed rational adaptation
of Matthew J. Colbrook's counterexample method. Formalization: Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. AI-assisted formalization.
-/
import NLA.MI22.ExactData
import NLA.MI22.SingularValues
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix
noncomputable section
namespace NLA.MI22

theorem witnessVector_norm : ‖witnessVector‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [witnessVector, Fin.sum_univ_succ, norm_div]

theorem witness_rational_data_proved :
    witnessT = witnessLDL * witnessPivots * witnessLDL.conjTranspose ∧
    witnessA = Matrix.diagonal (![256, 1 / 256, 1] : Fin 3 → ℂ) ∧
    witnessT.PosDef ∧ witnessA.PosDef ∧ witnessB.PosDef ∧
    ‖witnessVector‖ = 1 ∧
    witnessB.trace.re < (4 : ℝ) ^ (8 : ℕ) ∧
    44000 < witnessTestValue ∧
    frobeniusSquared (witnessA * witnessB) < (10500 : ℝ) ^ (2 : ℕ) :=
  ⟨witnessT_ldl, witnessA_diagonal, witnessT_posDef, witnessA_posDef,
    witnessB_posDef, witnessVector_norm, witnessB_trace_lt,
    witnessTestValue_gt, witnessAB_frobeniusSquared_lt⟩

theorem witnessRoot_norm_lt : operatorNorm witnessRoot < 4 := by
  have hpow : operatorNorm witnessRoot ^ (8 : ℕ) < (4 : ℝ) ^ (8 : ℕ) := by
    rw [← operatorNorm_eighth_power _ witnessRoot_posDef.isHermitian,
      witnessRoot_pow_eight]
    exact (operatorNorm_posSemidef_le_trace _ witnessB_posDef.posSemidef).trans_lt
      witnessB_trace_lt
  by_contra! h
  exact (not_le_of_gt hpow) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 4) h 8)

theorem witness_principal_powers_proved :
    spectralPower witnessA (1 / 2) = witnessD ∧
    spectralPower witnessA (-1 / 2) = witnessDInv ∧
    spectralPower witnessA (1 / 8) = witnessAOneEighth ∧
    spectralPower witnessA (5 / 8) = witnessAFiveEighths ∧
    spectralPower (witnessDInv * witnessB * witnessDInv) (1 / 8) = witnessT ∧
    weightedMean witnessA witnessB (1 / 8) = witnessD * witnessT * witnessD ∧
    witnessRoot.PosDef ∧ witnessRoot ^ (8 : ℕ) = witnessB ∧
    spectralPower witnessB (7 / 8) * witnessRoot = witnessB ∧
    leftProduct witnessA witnessB (1 / 8) * witnessRoot = witnessN ∧
    operatorNorm witnessRoot < 4 :=
  ⟨witnessA_half, witnessA_negative_half, witnessA_eighth, witnessA_five_eighths,
    witness_normalized_root, witness_weightedMean, witnessRoot_posDef,
    witnessRoot_pow_eight, witnessRoot_right_factor, witness_left_mul_root,
    witnessRoot_norm_lt⟩

theorem witness_operator_gap_proved :
    operatorNorm (witnessA * witnessB) < 10500 ∧
    11000 < operatorNorm (leftProduct witnessA witnessB (1 / 8)) := by
  constructor
  · have hu := (euclidean_norm_bounds_proved (witnessA * witnessB)).1
    have hf := witnessAB_frobeniusSquared_lt
    have hn := operatorNorm_nonneg (witnessA * witnessB)
    nlinarith
  · have htest : witnessTestValue ≤ operatorNorm witnessN := by
      have h := (euclidean_norm_bounds_proved witnessN).2 witnessVector 0
      rw [witnessVector_norm, mul_one] at h
      exact (Complex.re_le_norm _).trans h
    have hmul : operatorNorm witnessN ≤
        operatorNorm (leftProduct witnessA witnessB (1 / 8)) * operatorNorm witnessRoot := by
      rw [← witness_left_mul_root]
      exact operatorNorm_mul _ _
    have hl := witnessTestValue_gt.trans_le (htest.trans hmul)
    by_contra! h
    have hu : operatorNorm (leftProduct witnessA witnessB (1 / 8)) *
        operatorNorm witnessRoot ≤ (11000 : ℝ) * 4 :=
      mul_le_mul h witnessRoot_norm_lt.le (operatorNorm_nonneg witnessRoot) (by norm_num)
    norm_num at hu
    exact (not_le_of_gt hl) hu

/-- The single numerical interval task is a point inequality, explicitly
kernel-checked and consumed in the strict singular-value reversal below. -/
theorem numerical_separation : (10500 : ℝ) < 11000 := by
  interval_decide (trust := kernel)

theorem counterexample_proved :
    witnessA.PosDef ∧ witnessB.PosDef ∧
    (0 : ℝ) ≤ 1 / 8 ∧ (1 / 8 : ℝ) ≤ 1 ∧
    singularValue (witnessA * witnessB) 0 <
      singularValue (leftProduct witnessA witnessB (1 / 8)) 0 ∧
    ¬ SingularLogMajorized (leftProduct witnessA witnessB (1 / 8))
      (witnessA * witnessB) := by
  have hgap : singularValue (witnessA * witnessB) 0 <
      singularValue (leftProduct witnessA witnessB (1 / 8)) 0 := by
    rw [singularValue_zero_eq_operatorNorm (by norm_num),
      singularValue_zero_eq_operatorNorm (by norm_num)]
    exact witness_operator_gap_proved.1.trans
      (numerical_separation.trans witness_operator_gap_proved.2)
  refine ⟨witnessA_posDef, witnessB_posDef, by norm_num, by norm_num, hgap, ?_⟩
  intro h
  have hfirst := h.1 1 (by norm_num) (by norm_num)
  simp only [singularPrefix, Finset.prod_range_succ, Finset.prod_range_zero,
    one_mul] at hfirst
  exact (not_le_of_gt hgap) hfirst

theorem not_weightedLogMajorizationConjecture_proved :
    ¬ WeightedLogMajorizationConjecture := by
  intro h
  exact counterexample_proved.2.2.2.2.2
    (h 3 (by norm_num) witnessA witnessB witnessA_posDef witnessB_posDef
      (1 / 8) (by norm_num) (by norm_num))

#assert_trust kernel singular_values_semantics_proved
#assert_trust kernel spectral_power_semantics_proved
#assert_trust kernel euclidean_norm_bounds_proved
#assert_trust kernel witness_rational_data_proved
#assert_trust kernel witness_principal_powers_proved
#assert_trust kernel witness_operator_gap_proved
#assert_trust kernel numerical_separation
#assert_trust kernel counterexample_proved
#assert_trust kernel not_weightedLogMajorizationConjecture_proved

#print axioms singular_values_semantics_proved
#print axioms spectral_power_semantics_proved
#print axioms euclidean_norm_bounds_proved
#print axioms witness_rational_data_proved
#print axioms witness_principal_powers_proved
#print axioms witness_operator_gap_proved
#print axioms numerical_separation
#print axioms counterexample_proved
#print axioms not_weightedLogMajorizationConjecture_proved

end NLA.MI22
