import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# Limits controlled by an inverse-square derivative

An integrable derivative bounded by `C/r²` gives a finite limit with error
`C/r`. This is the scalar tail estimate for the rotating oscillator coefficients.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace ProofProject

/-- No minimizer or implicit asymptotic constant is assumed: the limit follows
from the actual derivative and its integrable power bound. -/
theorem exists_limit_of_deriv_le_inv_sq {f g : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (hf : ∀ r, 1 ≤ r → HasDerivAt f (g r) r)
    (hg : ContinuousOn g (Ici 1))
    (hb : ∀ r, 1 ≤ r → |g r| ≤ C * r ^ (-2 : ℝ)) :
    ∃ A : ℝ, Tendsto f atTop (𝓝 A) ∧ ∀ r, 1 ≤ r → |f r - A| ≤ C / r := by
  have hgi : IntegrableOn g (Ioi 1) := by
    apply (((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1))).const_mul C).mono'
      ((hg.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    simpa only [Real.norm_eq_abs] using hb r hr.le
  have ht := tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (fun r hr => hf r hr.le) hgi
  refine ⟨limUnder atTop f, ht, ?_⟩
  intro r hr
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hgr : IntegrableOn g (Ioi r) := hgi.mono_set (fun s hs => lt_of_le_of_lt hr hs)
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => hf s (hr.trans hs)) hgr ht
  calc
    |f r - limUnder atTop f| = ‖∫ s in Ioi r, g s‖ := by
      rw [heq, Real.norm_eq_abs, abs_sub_comm]
    _ ≤ ∫ s in Ioi r, C * s ^ (-2 : ℝ) := by
      apply norm_integral_le_of_norm_le
        ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr0).const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      simpa only [Real.norm_eq_abs] using hb s (hr.trans hs.le)
    _ = C / r := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hr0]
      norm_num [Real.rpow_neg_one, div_eq_mul_inv]

end ProofProject
