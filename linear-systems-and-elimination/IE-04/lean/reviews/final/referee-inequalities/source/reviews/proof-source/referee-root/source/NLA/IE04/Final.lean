/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The complete original uniform exponential-tail claim is contradicted for
every pair of positive real constants. The genuine identity center has
Euclidean operator norm one, noise scale is one, and all admissible rules
violate the proposed tail in the same chosen dimension and threshold.
-/
import NLA.IE04.ProbabilityTail
import NLA.IE04.Asymptotics
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem identity_spectralNorm {n : ℕ} (hn : 1 ≤ n) : spectralNorm (1 : Mat n) = 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  unfold spectralNorm
  exact norm_one

theorem threshold_times_rpow {n : ℕ} (hn : 1 ≤ n) (c₁ : ℝ) :
    contradictionThreshold n c₁ * (n : ℝ) ^ c₁ = growthThreshold n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpow : (n : ℝ) ^ c₁ ≠ 0 := (Real.rpow_pos_of_pos hnpos c₁).ne'
  unfold contradictionThreshold growthThreshold
  field_simp

theorem dyadic_tail_strict {n : ℕ} (c₂ x : ℝ)
    (h : (probabilityExponent n : ℝ) < c₂ * x) :
    ENNReal.ofReal ((2 : ℝ) ^ (-c₂ * x)) <
      ENNReal.ofReal (1 / (2 : ℝ) ^ probabilityExponent n) := by
  have hpow : (2 : ℝ) ^ (-c₂ * x) < (2 : ℝ) ^ (-(probabilityExponent n : ℝ)) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast] at hpow
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  simpa only [one_div] using hpow

theorem counterexample (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ∃ n : ℕ, 2 ≤ n ∧ ∃ x : ℝ, 1 ≤ x ∧ spectralNorm (1 : Mat n) = 1 ∧
      ∀ rule : Mat n → PivotPath n, AdmissibleRule rule →
        ENNReal.ofReal ((2 : ℝ) ^ (-c₂ * x)) <
          gaussianMatrix n (exceedanceEvent (1 : Mat n) 1 (x * (n : ℝ) ^ c₁) rule) := by
  obtain ⟨n, hn, hx, hexponent⟩ := contradiction_dimension c₁ c₂ hc₁ hc₂
  refine ⟨n, hn, contradictionThreshold n c₁, hx,
    identity_spectralNorm (by omega), ?_⟩
  intro rule hrule
  rw [threshold_times_rpow (by omega) c₁]
  exact (dyadic_tail_strict c₂ _ hexponent).trans_le (gepp_gaussian_tail_lower hn rule hrule)

theorem not_uniformExponentialTail : ¬ UniformExponentialTail := by
  rintro ⟨c₁, c₂, hc₁, hc₂, hbound⟩
  obtain ⟨n, hn, x, hx, hnorm, hlower⟩ := counterexample c₁ c₂ hc₁ hc₂
  have hupper := hbound n (by omega) (1 : Mat n) hnorm.le
    1 (by norm_num) le_rfl x hx (@firstPath n) (firstPath_admissibleRule_proved n)
  have hlower' := hlower (@firstPath n) (firstPath_admissibleRule_proved n)
  simp only [div_one] at hupper
  exact (not_lt_of_ge hupper) hlower'

#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_uniformExponentialTail
#print axioms not_uniformExponentialTail

end NLA.IE04
