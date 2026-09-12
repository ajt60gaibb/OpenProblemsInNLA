/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-23.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI23.Arithmetic

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI23

theorem witness_data_proved :
    witnessD.PosDef ∧ witnessT.PosDef ∧ witnessA.PosDef ∧ witnessB.PosDef ∧
      witnessG.PosDef ∧ witnessH.PosDef ∧
      witnessT = witnessL * witnessPivots * witnessL.conjTranspose ∧
      spectralPower witnessA (1 / 2) = witnessD ∧
      spectralPower witnessA (-1 / 2) = witnessDInv ∧
      spectralPower witnessA (-1 / 2) * witnessB *
        spectralPower witnessA (-1 / 2) = witnessT ^ (8 : ℕ) ∧
      generalizedMean witnessA witnessB 1 (1 / 8) = witnessG ∧
      generalizedMean witnessA witnessB 1 (7 / 8) = witnessH ∧
      leftProduct witnessA witnessB 1 1 2 (1 / 8) =
        witnessG ^ (2 : ℕ) * witnessH ^ (2 : ℕ) ∧
      rightProduct witnessA witnessB 1 1 2 =
        witnessA ^ (2 : ℕ) * witnessB ^ (2 : ℕ) :=
  ⟨witnessD_posDef, witnessT_posDef, witnessA_posDef, witnessB_posDef,
    witnessG_posDef, witnessH_posDef, witnessT_ldl, witnessA_half, witnessA_negative_half,
    witness_normalized_inner, witness_mean_eighth, witness_mean_seven_eighths,
    witness_left_product, witness_right_product⟩

theorem witness_squared_gap_proved :
    (witnessG * witnessH) 0 2 = (1260589125202 / 9 : ℂ) ∧
      frobeniusSquared (witnessA * witnessB) =
        (2009446159144992718181231562721 / 107495424 : ℝ) ∧
      Complex.normSq ((witnessG * witnessH) 0 2) -
        frobeniusSquared (witnessA * witnessB) = squaredGap ∧
      0 < squaredGap ∧ operatorNorm (witnessA * witnessB) ^ 2 <
        operatorNorm (witnessG * witnessH) ^ 2 :=
  ⟨witness_GH_entry, witness_frobenius_AB, witness_exact_gap, squaredGap_positive,
    witness_strict_norm_gap⟩

theorem witness_largest_strict_gap :
    largestEigenvalue (rightProduct witnessA witnessB 1 1 2) <
      largestEigenvalue (leftProduct witnessA witnessB 1 1 2 (1 / 8)) := by
  rw [witness_left_product, witness_right_product,
    squared_product_largest_proved (by norm_num) _ _ witnessA_posDef witnessB_posDef,
    squared_product_largest_proved (by norm_num) _ _ witnessG_posDef witnessH_posDef]
  exact witness_strict_norm_gap

theorem prefix_one_eq_largest {n : ℕ} (A : Mat n)
    (hlen : 1 ≤ (orderedEigenvalues A).length) :
    ((orderedEigenvalues A).take 1).prod = largestEigenvalue A := by
  unfold largestEigenvalue
  cases he : orderedEigenvalues A with
  | nil => simp only [he, List.length_nil] at hlen; omega
  | cons a l => simp

theorem witness_not_logMajorized :
    ¬ LogMajorized
      (orderedEigenvalues (leftProduct witnessA witnessB 1 1 2 (1 / 8)))
      (orderedEigenvalues (rightProduct witnessA witnessB 1 1 2)) := by
  have hleft : (orderedEigenvalues (leftProduct witnessA witnessB 1 1 2 (1 / 8))).length = 3 := by
    rw [witness_left_product]
    exact (product_eigenvalue_semantics_proved _ _
      (naturalPower_posDef _ witnessG_posDef 2)
      (naturalPower_posDef _ witnessH_posDef 2)).2.2.2.2.2.1
  have hright : (orderedEigenvalues (rightProduct witnessA witnessB 1 1 2)).length = 3 := by
    rw [witness_right_product]
    exact (product_eigenvalue_semantics_proved _ _
      (naturalPower_posDef _ witnessA_posDef 2)
      (naturalPower_posDef _ witnessB_posDef 2)).2.2.2.2.2.1
  intro h
  have hp := h.2.1 1 (by norm_num) (by rw [hleft]; norm_num)
  rw [prefix_one_eq_largest _ (by rw [hleft]; norm_num),
    prefix_one_eq_largest _ (by rw [hright]; norm_num)] at hp
  exact (not_le_of_gt witness_largest_strict_gap) hp

theorem counterexample_proved :
    witnessA.PosDef ∧ witnessB.PosDef ∧
      largestEigenvalue (rightProduct witnessA witnessB 1 1 2) <
        largestEigenvalue (leftProduct witnessA witnessB 1 1 2 (1 / 8)) ∧
      ¬ LogMajorized
        (orderedEigenvalues (leftProduct witnessA witnessB 1 1 2 (1 / 8)))
        (orderedEigenvalues (rightProduct witnessA witnessB 1 1 2)) :=
  ⟨witnessA_posDef, witnessB_posDef, witness_largest_strict_gap, witness_not_logMajorized⟩

theorem not_generalizedGeometricMeanConjecture_proved :
    ¬ GeneralizedGeometricMeanConjecture := by
  intro h
  exact witness_not_logMajorized (h 3 (by norm_num) witnessA witnessB
    witnessA_posDef witnessB_posDef 1 1 2 (1 / 8) (by norm_num) (by norm_num)
    (by norm_num) (Or.inl ⟨le_rfl, le_rfl⟩))

end NLA.MI23
