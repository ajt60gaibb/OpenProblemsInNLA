import NLA.TR07.SubsetDefect
import Mathlib.Analysis.SpecificLimits.Basic

/-! Elementary consequences of the two dimension-ratio assumptions. -/
noncomputable section
open Filter
open scoped Topology
namespace NLA.TR07

theorem aspect_ratio_bounds {C : ℝ} (hC : 1 ≤ C) {r : ℕ → ℕ}
    (hkr : Tendsto (fun k : ℕ => (k:ℝ)/(r k:ℝ)) atTop (𝓝 C)) :
    (∀ᶠ k in atTop, 0 < r k ∧ (2*C)⁻¹ * (k:ℝ) ≤ r k) ∧ Tendsto r atTop atTop := by
  have hC0 : 0 < C := by linarith
  have h2C : 0 < 2*C := by positivity
  have hev : ∀ᶠ k in atTop, 0 < r k ∧ (2*C)⁻¹ * (k:ℝ) ≤ r k := by
    filter_upwards [hkr.eventually (eventually_gt_nhds hC0),
      hkr.eventually (eventually_lt_nhds (show C < 2*C by linarith))] with k hlo hhi
    have hr : 0 < r k := by
      by_contra hn
      have hz : r k = 0 := by omega
      simp [hz] at hlo
    have hrR : (0:ℝ) < r k := by exact_mod_cast hr
    refine ⟨hr, ?_⟩
    have hh := (div_lt_iff₀ hrR).mp hhi
    rw [inv_mul_eq_div]
    exact (div_le_iff₀ h2C).mpr (by nlinarith)
  refine ⟨hev, (tendsto_natCast_atTop_iff (R := ℝ)).mp ?_⟩
  exact tendsto_atTop_mono' atTop (hev.mono (fun _ h => h.2))
    (Tendsto.const_mul_atTop (inv_pos.mpr h2C) tendsto_natCast_atTop_atTop)

theorem sample_fraction_tendsto_zero {r n : ℕ → ℕ}
    (hnr : Tendsto (fun k => (n k:ℝ)/(r k:ℝ)) atTop atTop) :
    Tendsto (fun k => (r k:ℝ)/(n k:ℝ)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, inv_div] using tendsto_inv_atTop_zero.comp hnr

theorem probability_bound_tendsto_zero {r n : ℕ → ℕ} (hr : Tendsto r atTop atTop)
    (hnr : Tendsto (fun k => (n k:ℝ)/(r k:ℝ)) atTop atTop) (ρ : ℝ) :
    Tendsto (fun k => (4/ρ^2) * (r k:ℝ)⁻¹ + ρ⁻¹ * ((r k:ℝ)/(n k:ℝ)))
      atTop (𝓝 0) := by
  have hr0 : Tendsto (fun k => (r k:ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hr)
  simpa using (hr0.const_mul (4/ρ^2)).add ((sample_fraction_tendsto_zero hnr).const_mul ρ⁻¹)

theorem subsetTail_le_simplified {k n r : ℕ} (M : Mat k n) (η : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ)
    (h : subsetTail M r η ≤ 4/(ρ^2*r) + (r-1)/(ρ*n)) :
    subsetTail M r η ≤ (4/ρ^2)*(r:ℝ)⁻¹ + ρ⁻¹*((r:ℝ)/(n:ℝ)) := by
  apply h.trans
  calc
    _ ≤ 4/(ρ^2*r) + (r:ℝ)/(ρ*n) := by
      apply add_le_add_right
      apply div_le_div_of_nonneg_right (by linarith) (mul_nonneg hρ.le (Nat.cast_nonneg _))
    _ = _ := by ring

end NLA.TR07
