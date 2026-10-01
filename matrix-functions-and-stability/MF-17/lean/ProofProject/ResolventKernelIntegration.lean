import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# Scalar integration by parts for the exponential resolvent kernel

The boundary term at zero is retained explicitly. It disappears only under the
additional hypothesis `k 0 = 0`. These scalar identities do not assert any
operator convolution identity. The calculation is valid for every real rate,
so in particular for the positive rates used in the source.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

/-- Differentiation in the integration variable gives a positive factor `r`. -/
lemma resolventKernel_hasDerivAt (r v u : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (-r * (v - s)) : ℂ))
      ((r : ℂ) * (Real.exp (-r * (v - u)) : ℂ)) u := by
  have hd : HasDerivAt (fun s : ℝ => -r * (v - s)) r u := by
    simpa only [id_eq, neg_mul, mul_neg, mul_one, neg_neg] using
      ((hasDerivAt_id u).const_sub v).const_mul (-r)
  simpa only [Complex.ofReal_mul, mul_comm] using hd.exp.ofReal_comp

/-- Integration by parts with the full endpoint contribution. Integrability of
the derivative suffices; continuity of the derivative is not needed. -/
theorem resolventKernel_integration_by_parts (r : ℝ) {v : ℝ} (hv : 0 ≤ v)
    {k k' : ℝ → ℂ}
    (hk : ∀ u ∈ Icc 0 v, HasDerivAt k (k' u) u)
    (hk' : IntervalIntegrable k' volume 0 v) :
    (r : ℂ) * (∫ u in (0 : ℝ)..v, (Real.exp (-r * (v - u)) : ℂ) * k' u) =
      (r : ℂ) * k v - (r : ℂ) * (Real.exp (-r * v) : ℂ) * k 0 -
        (r : ℂ) ^ 2 * (∫ u in (0 : ℝ)..v,
          (Real.exp (-r * (v - u)) : ℂ) * k u) := by
  let w : ℝ → ℂ := fun u => (Real.exp (-r * (v - u)) : ℂ)
  have hw (u : ℝ) : HasDerivAt w ((r : ℂ) * w u) u :=
    resolventKernel_hasDerivAt r v u
  have hc : Continuous w := continuous_iff_continuousAt.mpr
    (fun u => (hw u).continuousAt)
  have hi : IntervalIntegrable (fun u => (r : ℂ) * w u) volume 0 v :=
    (continuous_const.mul hc).intervalIntegrable 0 v
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun u (_ : u ∈ uIcc 0 v) => hw u)
    (fun u hu => hk u (by simpa only [uIcc_of_le hv] using hu)) hi hk'
  simp_rw [mul_assoc] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hwv : w v = 1 := by simp [w]
  have hw0 : w 0 = (Real.exp (-r * v) : ℂ) := by simp [w]
  rw [hwv, one_mul, hw0] at h
  calc
    (r : ℂ) * (∫ u in (0 : ℝ)..v, w u * k' u) =
        (r : ℂ) * (k v - (Real.exp (-r * v) : ℂ) * k 0 -
          (r : ℂ) * (∫ u in (0 : ℝ)..v, w u * k u)) := congrArg ((r : ℂ) * ·) h
    _ = _ := by
      change _ = (r : ℂ) * k v -
        (r : ℂ) * (Real.exp (-r * v) : ℂ) * k 0 -
        (r : ℂ) ^ 2 * (∫ u in (0 : ℝ)..v, w u * k u)
      ring

/-- The source formula follows when the kernel vanishes at zero. -/
theorem resolventKernel_integration_by_parts_of_zero (r : ℝ) {v : ℝ} (hv : 0 ≤ v)
    {k k' : ℝ → ℂ}
    (hk : ∀ u ∈ Icc 0 v, HasDerivAt k (k' u) u)
    (hk' : IntervalIntegrable k' volume 0 v) (hk0 : k 0 = 0) :
    (r : ℂ) * (∫ u in (0 : ℝ)..v, (Real.exp (-r * (v - u)) : ℂ) * k' u) =
      (r : ℂ) * k v - (r : ℂ) ^ 2 *
        (∫ u in (0 : ℝ)..v, (Real.exp (-r * (v - u)) : ℂ) * k u) := by
  simpa only [hk0, mul_zero, sub_zero] using
    resolventKernel_integration_by_parts r hv hk hk'

/-- A continuously differentiable kernel meets the integration hypotheses. -/
theorem resolventKernel_integration_by_parts_of_continuous (r : ℝ) {v : ℝ}
    (hv : 0 ≤ v) {k k' : ℝ → ℂ}
    (hk : ∀ u ∈ Icc 0 v, HasDerivAt k (k' u) u)
    (hk' : ContinuousOn k' (Icc 0 v)) :
    (r : ℂ) * (∫ u in (0 : ℝ)..v, (Real.exp (-r * (v - u)) : ℂ) * k' u) =
      (r : ℂ) * k v - (r : ℂ) * (Real.exp (-r * v) : ℂ) * k 0 -
        (r : ℂ) ^ 2 * (∫ u in (0 : ℝ)..v,
          (Real.exp (-r * (v - u)) : ℂ) * k u) := by
  exact resolventKernel_integration_by_parts r hv hk
    (ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hv] using hk'))

end ProofProject
