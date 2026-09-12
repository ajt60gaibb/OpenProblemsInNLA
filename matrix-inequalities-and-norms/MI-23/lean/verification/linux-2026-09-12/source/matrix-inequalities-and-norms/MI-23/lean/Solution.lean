/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Completed formalization of Matthew J. Colbrook's MI-23 counterexample.
The eight exports exactly restate the independently reviewed frozen Challenge.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI23.Proof
import LeanCert.Tactic.Verification

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI23

/-- Real powers and generalized means retain genuine positive definiteness,
including at negative and zero real exponents. -/
theorem positive_powers_and_means {n : ℕ} (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (r t : ℝ) :
    (spectralPower A r).PosDef ∧ (generalizedMean A B r t).PosDef := by
  exact positive_powers_and_means_proved A B hA hB r t

/-- An explicit invertible similarity to a positive definite matrix establishes
the full ordered-list semantics of every positive-definite product. -/
theorem product_eigenvalue_semantics {n : ℕ} (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    let R := spectralPower Y (1 / 2)
    let Rinv := spectralPower Y (-1 / 2)
    let S := R * X * R
    S.PosDef ∧ R * Rinv = 1 ∧ Rinv * R = 1 ∧
      R * (X * Y) * Rinv = S ∧ (X * Y).charpoly = S.charpoly ∧
      HasOrderedPositiveEigenvalues (X * Y) := by
  exact product_eigenvalue_semantics_proved X Y hX hY

/-- The actual first product eigenvalue equals the genuine squared Euclidean
operator norm. This is a theorem about the characteristic-polynomial list. -/
theorem squared_product_largest {n : ℕ} (hn : 1 ≤ n) (X Y : Mat n)
    (hX : X.PosDef) (hY : Y.PosDef) :
    largestEigenvalue (X ^ (2 : ℕ) * Y ^ (2 : ℕ)) = operatorNorm (X * Y) ^ 2 := by
  exact squared_product_largest_proved hn X Y hX hY

/-- Exact generic norm bounds; no entrywise matrix norm is substituted. -/
theorem operator_norm_bounds {n : ℕ} (X : Mat n) (i j : Fin n) :
    Complex.normSq (X i j) ≤ operatorNorm X ^ 2 ∧
      operatorNorm X ^ 2 ≤ frobeniusSquared X := by
  exact operator_norm_bounds_proved X i j

/-- Exact positivity and spectral-power identification of the rational witness.
All powers annotated by naturals are ordinary matrix products. -/
theorem witness_data :
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
        witnessA ^ (2 : ℕ) * witnessB ^ (2 : ℕ) := by
  exact witness_data_proved

/-- One exact complex entry and the complete Frobenius sum imply a strict genuine
operator-norm separation. The positive rational gap must be certified in kernel. -/
theorem witness_squared_gap :
    (witnessG * witnessH) 0 2 = (1260589125202 / 9 : ℂ) ∧
      frobeniusSquared (witnessA * witnessB) =
        (2009446159144992718181231562721 / 107495424 : ℝ) ∧
      Complex.normSq ((witnessG * witnessH) 0 2) -
        frobeniusSquared (witnessA * witnessB) = squaredGap ∧
      0 < squaredGap ∧ operatorNorm (witnessA * witnessB) ^ 2 <
        operatorNorm (witnessG * witnessH) ^ 2 := by
  exact witness_squared_gap_proved

/-- The fixed admissible pair violates the actual first ordered eigenvalue
inequality, and hence the complete original log-majorization relation. -/
theorem counterexample :
    witnessA.PosDef ∧ witnessB.PosDef ∧
      largestEigenvalue (rightProduct witnessA witnessB 1 1 2) <
        largestEigenvalue (leftProduct witnessA witnessB 1 1 2 (1 / 8)) ∧
      ¬ LogMajorized
        (orderedEigenvalues (leftProduct witnessA witnessB 1 1 2 (1 / 8)))
        (orderedEigenvalues (rightProduct witnessA witnessB 1 1 2)) := by
  exact counterexample_proved

/-- Full negative answer with no additional assumptions on the original target. -/
theorem not_generalizedGeometricMeanConjecture :
    ¬ GeneralizedGeometricMeanConjecture := by
  exact not_generalizedGeometricMeanConjecture_proved

/- Every exported and material internal theorem uses only the standard three
   axioms. Private finite certificates are included transitively in these checks. -/
#assert_trust kernel witness_GH_entry
#print axioms witness_GH_entry
#assert_trust kernel witness_frobenius_AB
#print axioms witness_frobenius_AB
#assert_trust kernel witness_exact_gap
#print axioms witness_exact_gap
#assert_trust kernel scalar_gap_positive
#print axioms scalar_gap_positive
#assert_trust kernel squaredGap_positive
#print axioms squaredGap_positive
#assert_trust kernel witness_strict_norm_gap
#print axioms witness_strict_norm_gap
#assert_trust kernel spectralPower_posDef
#print axioms spectralPower_posDef
#assert_trust kernel sandwich_posDef
#print axioms sandwich_posDef
#assert_trust kernel positive_powers_and_means_proved
#print axioms positive_powers_and_means_proved
#assert_trust kernel ordered_eigenvalues_posDef
#print axioms ordered_eigenvalues_posDef
#assert_trust kernel orderedEigenvalues_congr
#print axioms orderedEigenvalues_congr
#assert_trust kernel positive_eigenvalues_of_charpoly_eq
#print axioms positive_eigenvalues_of_charpoly_eq
#assert_trust kernel spectralPower_add
#print axioms spectralPower_add
#assert_trust kernel spectralPower_nat
#print axioms spectralPower_nat
#assert_trust kernel spectralPower_one
#print axioms spectralPower_one
#assert_trust kernel naturalPower_posDef
#print axioms naturalPower_posDef
#assert_trust kernel product_eigenvalue_semantics_proved
#print axioms product_eigenvalue_semantics_proved
#assert_trust kernel entry_le_operatorNorm
#print axioms entry_le_operatorNorm
#assert_trust kernel operatorNorm_posSemidef_le_trace
#print axioms operatorNorm_posSemidef_le_trace
#assert_trust kernel trace_gram_eq_frobeniusSquared
#print axioms trace_gram_eq_frobeniusSquared
#assert_trust kernel operatorNorm_sq_le_frobeniusSquared
#print axioms operatorNorm_sq_le_frobeniusSquared
#assert_trust kernel operator_norm_bounds_proved
#print axioms operator_norm_bounds_proved
#assert_trust kernel witness_data_proved
#print axioms witness_data_proved
#assert_trust kernel witness_squared_gap_proved
#print axioms witness_squared_gap_proved
#assert_trust kernel witness_largest_strict_gap
#print axioms witness_largest_strict_gap
#assert_trust kernel prefix_one_eq_largest
#print axioms prefix_one_eq_largest
#assert_trust kernel witness_not_logMajorized
#print axioms witness_not_logMajorized
#assert_trust kernel counterexample_proved
#print axioms counterexample_proved
#assert_trust kernel not_generalizedGeometricMeanConjecture_proved
#print axioms not_generalizedGeometricMeanConjecture_proved
#assert_trust kernel orderedEigenvalues_multiset
#print axioms orderedEigenvalues_multiset
#assert_trust kernel largestEigenvalue_spec
#print axioms largestEigenvalue_spec
#assert_trust kernel operatorNorm_eq_eigenvalueNorm
#print axioms operatorNorm_eq_eigenvalueNorm
#assert_trust kernel largestEigenvalue_posDef_eq_norm
#print axioms largestEigenvalue_posDef_eq_norm
#assert_trust kernel squared_product_largest_proved
#print axioms squared_product_largest_proved
#assert_trust kernel witnessD_posDef
#print axioms witnessD_posDef
#assert_trust kernel witnessPivots_posDef
#print axioms witnessPivots_posDef
#assert_trust kernel witnessL_det
#print axioms witnessL_det
#assert_trust kernel witnessL_isUnit
#print axioms witnessL_isUnit
#assert_trust kernel witnessT_ldl
#print axioms witnessT_ldl
#assert_trust kernel witnessT_posDef
#print axioms witnessT_posDef
#assert_trust kernel witnessA_posDef
#print axioms witnessA_posDef
#assert_trust kernel witnessB_posDef
#print axioms witnessB_posDef
#assert_trust kernel witnessG_posDef
#print axioms witnessG_posDef
#assert_trust kernel witnessH_posDef
#print axioms witnessH_posDef
#assert_trust kernel spectralPower_naturalPower
#print axioms spectralPower_naturalPower
#assert_trust kernel witnessA_half
#print axioms witnessA_half
#assert_trust kernel witnessD_mul_inv
#print axioms witnessD_mul_inv
#assert_trust kernel witnessD_inv_mul
#print axioms witnessD_inv_mul
#assert_trust kernel witnessA_negative_half
#print axioms witnessA_negative_half
#assert_trust kernel witness_normalized_inner
#print axioms witness_normalized_inner
#assert_trust kernel witnessT_eighth_root
#print axioms witnessT_eighth_root
#assert_trust kernel witnessT_seven_eighths
#print axioms witnessT_seven_eighths
#assert_trust kernel witness_mean_eighth
#print axioms witness_mean_eighth
#assert_trust kernel witness_mean_seven_eighths
#print axioms witness_mean_seven_eighths
#assert_trust kernel witness_left_product
#print axioms witness_left_product
#assert_trust kernel witness_right_product
#print axioms witness_right_product
#assert_trust kernel positive_powers_and_means
#print axioms positive_powers_and_means
#assert_trust kernel product_eigenvalue_semantics
#print axioms product_eigenvalue_semantics
#assert_trust kernel squared_product_largest
#print axioms squared_product_largest
#assert_trust kernel operator_norm_bounds
#print axioms operator_norm_bounds
#assert_trust kernel witness_data
#print axioms witness_data
#assert_trust kernel witness_squared_gap
#print axioms witness_squared_gap
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_generalizedGeometricMeanConjecture
#print axioms not_generalizedGeometricMeanConjecture

end NLA.MI23
