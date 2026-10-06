import NLA.IE06.Statements
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Conditional analytic reduction only. No result in this file proves the
all-Schur random-matrix tail assumed by the final theorem. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter
noncomputable section

namespace NLA.IE06

/-- Exact deterministic threshold comparison from the reviewed specification.
The logarithm lower bound is explicit; no numerical approximation is used. -/
theorem subpower_threshold_le_proved (C η x : ℝ) (hC : 0 ≤ C)
    (hη : 0 < η) (hx : 1 ≤ x)
    (hlog : (C / η) ^ 2 ≤ Real.log x) :
    Real.sqrt x * Real.exp (C * Real.sqrt (Real.log x)) ≤
      x ^ ((1 : ℝ) / 2 + η) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hquot : C / η ≤ Real.sqrt (Real.log x) :=
    (Real.le_sqrt (div_nonneg hC hη.le) hlognonneg).2 hlog
  have hCbound : C ≤ Real.sqrt (Real.log x) * η :=
    (div_le_iff₀ hη).1 hquot
  have hproduct := mul_le_mul_of_nonneg_right hCbound
    (Real.sqrt_nonneg (Real.log x))
  have hexponent : C * Real.sqrt (Real.log x) ≤ Real.log x * η := by
    nlinarith [Real.sq_sqrt hlognonneg]
  calc
    Real.sqrt x * Real.exp (C * Real.sqrt (Real.log x)) ≤
        Real.sqrt x * Real.exp (Real.log x * η) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (Real.sqrt_nonneg x)
    _ = x ^ ((1 : ℝ) / 2 + η) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_def_of_pos hxpos η, Real.rpow_add hxpos]

/-- The source rate threshold is eventually below every retained exponent. -/
theorem subpower_threshold_eventually_le_proved (C η : ℝ)
    (hC : 0 ≤ C) (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      Real.sqrt (n : ℝ) * Real.exp (C * Real.sqrt (Real.log (n : ℝ))) ≤
        (n : ℝ) ^ ((1 : ℝ) / 2 + η) := by
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop ((C / η) ^ 2)),
    eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  exact subpower_threshold_le_proved C η (n : ℝ) hC hη (by exact_mod_cast hnpos) hn

/-- The complete all-Schur quantitative proposition implies the original IE-06
limit. The random-matrix source bound is an explicit, unproved hypothesis. -/
theorem squareRootUpperBound_of_schurSubpolynomialTail_proved
    (hsource : SchurSubpolynomialTail) : SquareRootUpperBound := by
  intro η hη
  obtain ⟨C, hC, N, _hN, htail⟩ := hsource 1 zero_lt_one
  have hthreshold := subpower_threshold_eventually_le_proved C η hC.le hη
  have hprob :
      ∀ᶠ n : ℕ in atTop,
        gaussianMatrix n (exceedanceEvent n ((n : ℝ) ^ ((1 : ℝ) / 2 + η))) ≤
          ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ))) := by
    filter_upwards [hthreshold, eventually_ge_atTop N] with n hbound hn
    refine le_trans (MeasureTheory.measure_mono ?_) (htail n hn).le
    intro A hA
    rcases hA with ⟨hdim, hdet, path, hpath, hgrowth⟩
    exact ⟨hdim, hdet, path, hpath, lt_of_le_of_lt hbound hgrowth⟩
  have hlimit :
      Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) ^ (-(1 : ℝ))))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      ((tendsto_rpow_neg_atTop zero_lt_one).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hlimit (Eventually.of_forall fun _ => bot_le) hprob

#assert_trust kernel subpower_threshold_le_proved
#assert_trust kernel subpower_threshold_eventually_le_proved
#assert_trust kernel squareRootUpperBound_of_schurSubpolynomialTail_proved
#print axioms subpower_threshold_le_proved
#print axioms subpower_threshold_eventually_le_proved
#print axioms squareRootUpperBound_of_schurSubpolynomialTail_proved

end NLA.IE06
