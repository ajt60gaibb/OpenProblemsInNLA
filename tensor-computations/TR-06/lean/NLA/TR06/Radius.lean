/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.Density

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Filter Metric

namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- One radius controls both volume distortion and variation of the rectangular
Jacobian. All volume statements concern arbitrary subsets, including infinite ones. -/
theorem exists_volume_radius (A : E →L[ℝ] F) (hA : Injective A)
    {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      (∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ →
        |B.toLinearMap.normDet - A.toLinearMap.normDet| ≤ ε) ∧
      (∀ (s : Set E) (g : E → F), ApproximatesLinearOn g A s δ →
        μHE[Module.finrank ℝ E] (g '' s) ≤
          (ENNReal.ofReal A.toLinearMap.normDet + ε) * volume s) ∧
      (∀ (s : Set E) (g : E → F), ApproximatesLinearOn g A s δ →
        ENNReal.ofReal A.toLinearMap.normDet * volume s ≤
          μHE[Module.finrank ℝ E] (g '' s) + ε * volume s) := by
  let j : ℝ≥0 := Real.toNNReal A.toLinearMap.normDet
  have hjne : A.toLinearMap.normDet ≠ 0 := by
    exact ((A.toLinearMap.normDet_ne_zero_tfae).out 1 0).mp (LinearMap.ker_eq_bot.mpr hA)
  have hjpos : 0 < j := Real.toNNReal_pos.mpr (lt_of_le_of_ne
    A.toLinearMap.normDet_nonneg (Ne.symm hjne))
  have hupper : ENNReal.ofReal A.toLinearMap.normDet < (j + ε : ℝ≥0) := by
    change (j : ℝ≥0∞) < (j + ε : ℝ≥0)
    exact_mod_cast lt_add_of_pos_right j hε
  have hlower : ((j - ε : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal A.toLinearMap.normDet := by
    change ((j - ε : ℝ≥0) : ℝ≥0∞) < j
    exact_mod_cast tsub_lt_self hjpos hε
  obtain ⟨δ₀, hU, hL, hδ₀⟩ :=
    ((euclidean_image_le_mul_of_normDet_lt A hA hupper).and
      ((mul_le_euclidean_image_of_lt_normDet A hA hlower).and self_mem_nhdsWithin)).exists
  change 0 < δ₀ at hδ₀
  obtain ⟨δ₁, hδ₁, hclose⟩ := continuousAt_iff.mp
    (continuous_normDet (E := E) (F := F)).continuousAt (ε : ℝ) (by exact_mod_cast hε)
  let δ₂ : ℝ≥0 := ⟨δ₁ / 2, (half_pos hδ₁).le⟩
  refine ⟨min δ₀ δ₂, lt_min hδ₀ (half_pos hδ₁), ?_, ?_, ?_⟩
  · intro B hB
    apply le_of_lt
    apply hclose
    rw [dist_eq_norm]
    have hB₂ : ‖B - A‖ ≤ (δ₂ : ℝ) := hB.trans (by exact_mod_cast min_le_right δ₀ δ₂)
    exact hB₂.trans_lt (half_lt_self hδ₁)
  · intro s g hg
    have h := hU s g (hg.mono_num (min_le_left _ _))
    change μHE[Module.finrank ℝ E] (g '' s) ≤ ((j : ℝ≥0∞) + ε) * volume s
    simpa only [ENNReal.coe_add] using h
  · intro s g hg
    by_cases hs : volume s = ⊤
    · simp [hs, hε.ne']
    have h := hL s g (hg.mono_num (min_le_left _ _))
    change ((j - ε : ℝ≥0) : ℝ≥0∞) * volume s ≤ _ at h
    rw [ENNReal.coe_sub, ENNReal.sub_mul, tsub_le_iff_right] at h
    · exact h
    · simp only [hs, imp_true_iff, ne_eq, not_false_eq_true]

#print axioms exists_volume_radius
#assert_trust kernel exists_volume_radius

end NLA.TR06.Area
