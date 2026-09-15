/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Numerator
import NLA.MF24.Energy
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

theorem polynomial_norm_ratio (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    Real.sqrt (m : ℝ) / (1 + (m : ℝ) / t ^ 2) ≤
      spectralNorm (polyEval (matrixX m t) (testPolynomial m)) /
        spectralNorm (polyEval (matrixY m t) (testPolynomial m)) := by
  have ht0 : 0 < t := by linarith
  have hden : 0 < t ^ 2 + (m : ℝ) := by positivity
  have hratio : 0 < 1 + (m : ℝ) / t ^ 2 := by positivity
  have hY := spectralNorm_pos (denominator_polynomial_ne_zero m hm t ht)
  calc
    Real.sqrt (m : ℝ) / (1 + (m : ℝ) / t ^ 2) =
        (t ^ 2 * Real.sqrt (m : ℝ)) / (t ^ 2 + (m : ℝ)) := by
      field_simp [ne_of_gt ht0, ne_of_gt hden, ne_of_gt hratio] <;> ring
    _ ≤ spectralNorm (polyEval (matrixX m t) (testPolynomial m)) / (t ^ 2 + (m : ℝ)) :=
      div_le_div_of_nonneg_right (polynomial_numerator_bound m hm t ht) hden.le
    _ ≤ spectralNorm (polyEval (matrixX m t) (testPolynomial m)) /
        spectralNorm (polyEval (matrixY m t) (testPolynomial m)) :=
      div_le_div_of_nonneg_left (spectralNorm_nonneg _) hY
        (polynomial_denominator_bound m hm t ht)

theorem finite_rational_family_ratio (m : ℕ) (hm : 2 ≤ m) :
    (2 / 3 : ℝ) * Real.sqrt (m : ℝ) ≤
      spectralNorm (polyEval (matrixX m (m : ℝ)) (testPolynomial m)) /
        spectralNorm (polyEval (matrixY m (m : ℝ)) (testPolynomial m)) := by
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hden : 0 < 1 + (m : ℝ) / (m : ℝ) ^ 2 := by positivity
  have hfrac : (m : ℝ) / (m : ℝ) ^ 2 ≤ 1 / 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hm0)).mpr
    nlinarith
  have hsmall : (2 / 3 : ℝ) * Real.sqrt (m : ℝ) ≤
      Real.sqrt (m : ℝ) / (1 + (m : ℝ) / (m : ℝ) ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ ((2 / 3 : ℝ) * Real.sqrt (m : ℝ)) * (3 / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = Real.sqrt (m : ℝ) := by ring
  exact hsmall.trans (polynomial_norm_ratio m hm (m : ℝ) hm1)

/-- The numerical divergence is an explicit finite natural-index witness.
The separate SIP theorem will supply the spectral hypothesis in the final
canonical result, without adding a limit or supremum assumption here. -/
lemma arbitrarily_large_norm_ratios (C : ℝ) (hC : 0 ≤ C) :
    ∃ m : ℕ, 2 ≤ m ∧
      polyEval (matrixY m (m : ℝ)) (testPolynomial m) ≠ 0 ∧
      C * spectralNorm (polyEval (matrixY m (m : ℝ)) (testPolynomial m)) <
        spectralNorm (polyEval (matrixX m (m : ℝ)) (testPolynomial m)) := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((3 * (C + 1)) ^ 2 + 2)
  have hmreal : (2 : ℝ) < (m : ℝ) := by nlinarith [sq_nonneg (3 * (C + 1))]
  have hm2 : 2 ≤ m := by exact_mod_cast hmreal.le
  have hm1 : (1 : ℝ) < (m : ℝ) := by linarith
  have hroot : 3 * (C + 1) < Real.sqrt (m : ℝ) :=
    Real.lt_sqrt_of_sq_lt (by linarith)
  have hlarge : C < (2 / 3 : ℝ) * Real.sqrt (m : ℝ) := by linarith
  have hYne := denominator_polynomial_ne_zero m hm2 (m : ℝ) hm1
  have hYpos := spectralNorm_pos hYne
  refine ⟨m, hm2, hYne, ?_⟩
  exact (lt_div_iff₀ hYpos).mp (hlarge.trans_le (finite_rational_family_ratio m hm2))

#assert_trust kernel polynomial_norm_ratio
#assert_trust kernel finite_rational_family_ratio
#assert_trust kernel arbitrarily_large_norm_ratios
#print axioms polynomial_norm_ratio
#print axioms finite_rational_family_ratio

end NLA.MF24
