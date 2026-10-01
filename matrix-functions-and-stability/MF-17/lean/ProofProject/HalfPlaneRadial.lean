import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Tactic

/-!
# The radial norm bound for holomorphic functions with nonnegative real part

The half-plane Möbius map and Schwarz's lemma give the exact factor
`(1+‖z‖)/(1-‖z‖)`. Adding a positive real constant and passing to zero includes
functions whose real part vanishes, without a strict-positivity assumption.
-/

noncomputable section

open Metric Set Filter
open scoped Topology

namespace ProofProject

lemma halfPlane_mobius_norm_sq_sub (u v : ℂ) :
    ‖u + starRingEnd ℂ v‖ ^ 2 - ‖u - v‖ ^ 2 = 4 * u.re * v.re := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

lemma halfPlane_mobius_norm_le {u v : ℂ} (hu : 0 ≤ u.re) (hv : 0 ≤ v.re) :
    ‖u - v‖ ≤ ‖u + starRingEnd ℂ v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hn : 0 ≤ 4 * u.re * v.re := by positivity
  rw [← halfPlane_mobius_norm_sq_sub] at hn
  linarith

/-- Strict positivity is needed only at the center for the Möbius denominator. -/
theorem halfPlane_norm_le_of_re_zero_pos {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hRe : ∀ w : ℂ, ‖w‖ < 1 → 0 ≤ (F w).re) (h0 : 0 < (F 0).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖F z‖ ≤ ‖F 0‖ * (1 + ‖z‖) / (1 - ‖z‖) := by
  let G : ℂ → ℂ := fun w => (F w - F 0) / (F w + starRingEnd ℂ (F 0))
  have hden (w : ℂ) (hw : ‖w‖ < 1) : F w + starRingEnd ℂ (F 0) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
    linarith [hRe w hw]
  have hG : DifferentiableOn ℂ G (ball 0 1) :=
    (hF.sub_const (F 0)).div (hF.add_const (starRingEnd ℂ (F 0)))
      (fun w hw => hden w (mem_ball_zero_iff.mp hw))
  have hmaps : MapsTo G (ball 0 1) (closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    change ‖(F w - F 0) / (F w + starRingEnd ℂ (F 0))‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr (hden w (mem_ball_zero_iff.mp hw)))]
    exact halfPlane_mobius_norm_le (hRe w (mem_ball_zero_iff.mp hw)) h0.le
  have hG0 : G 0 = 0 := by simp [G]
  have hs := Complex.norm_le_norm_of_mapsTo_ball hG hmaps hG0 hz
  change ‖(F z - F 0) / (F z + starRingEnd ℂ (F 0))‖ ≤ ‖z‖ at hs
  rw [norm_div] at hs
  have hdist := (div_le_iff₀ (norm_pos_iff.mpr (hden z hz))).mp hs
  have hadd := norm_add_le (F z) (starRingEnd ℂ (F 0))
  rw [RCLike.norm_conj] at hadd
  have hupper := mul_le_mul_of_nonneg_left hadd (norm_nonneg z)
  have hlower := norm_sub_norm_le (F z) (F 0)
  apply (le_div_iff₀ (sub_pos.mpr hz)).mpr
  nlinarith

/-- The complete half-plane radial estimate, including the zero-real-part and
zero-value cases. All hypotheses concern actual complex differentiability. -/
theorem halfPlane_norm_le {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (ball 0 1))
    (hRe : ∀ w : ℂ, ‖w‖ < 1 → 0 ≤ (F w).re)
    {z : ℂ} (hz : ‖z‖ < 1) :
    ‖F z‖ ≤ ‖F 0‖ * (1 + ‖z‖) / (1 - ‖z‖) := by
  have hleft : Tendsto (fun ε : ℝ => ‖F z + (ε : ℂ)‖) (𝓝[>] 0) (𝓝 ‖F z‖) := by
    have hc : ContinuousAt (fun ε : ℝ => ‖F z + (ε : ℂ)‖) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hright : Tendsto
      (fun ε : ℝ => ‖F 0 + (ε : ℂ)‖ * (1 + ‖z‖) / (1 - ‖z‖))
      (𝓝[>] 0) (𝓝 (‖F 0‖ * (1 + ‖z‖) / (1 - ‖z‖))) := by
    have hc : ContinuousAt
        (fun ε : ℝ => ‖F 0 + (ε : ℂ)‖ * (1 + ‖z‖) / (1 - ‖z‖)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  apply halfPlane_norm_le_of_re_zero_pos (hF.add_const (ε : ℂ)) _ _ hz
  · intro w hw
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hRe w hw]
  · simp only [Complex.add_re, Complex.ofReal_re]
    linarith [hRe 0 (by norm_num)]

end ProofProject
