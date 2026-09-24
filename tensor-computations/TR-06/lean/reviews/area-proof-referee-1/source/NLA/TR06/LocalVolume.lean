/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
import NLA.TR06.Rectangular

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology
open MeasureTheory Set Function Filter

namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

/-- Sharp local upper estimate for a rectangular injective linearization. -/
theorem euclidean_image_le_mul_of_normDet_lt (A : E →L[ℝ] F)
    (hA : Injective A) {c : ℝ≥0} (hc : ENNReal.ofReal A.toLinearMap.normDet < c) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set E) (f : E → F),
      ApproximatesLinearOn f A s δ →
        μHE[Module.finrank ℝ E] (f '' s) ≤ c * volume s := by
  obtain ⟨K, _hKpos, hK⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  let j : ℝ≥0 := Real.toNNReal A.toLinearMap.normDet
  have hjc : j < c := by
    change (j : ℝ≥0∞) < c at hc
    exact ENNReal.coe_lt_coe.mp hc
  have hlim : Tendsto (fun δ : ℝ≥0 => (1 + δ * K) ^ Module.finrank ℝ E * j)
      (𝓝 0) (𝓝 j) := by
    simpa only [zero_mul, add_zero, one_pow, one_mul] using
      (show Continuous (fun δ : ℝ≥0 => (1 + δ * K) ^ Module.finrank ℝ E * j) by fun_prop).tendsto 0
  have hevent := (tendsto_order.1 hlim).2 c hjc
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds] with δ hδ s f hf
  have hcoef : ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
      ENNReal.ofReal A.toLinearMap.normDet ≤ c := by
    change ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E * (j : ℝ≥0∞) ≤ c
    exact_mod_cast hδ.le
  calc
    _ ≤ ((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        (ENNReal.ofReal A.toLinearMap.normDet * volume s) :=
      approximation_euclidean_image_le hA hK hf
    _ = (((1 + δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        ENNReal.ofReal A.toLinearMap.normDet) * volume s := by rw [mul_assoc]
    _ ≤ _ := by gcongr

/-- Sharp local lower estimate for a rectangular injective linearization. -/
theorem mul_le_euclidean_image_of_lt_normDet (A : E →L[ℝ] F)
    (hA : Injective A) {c : ℝ≥0} (hc : (c : ℝ≥0∞) < ENNReal.ofReal A.toLinearMap.normDet) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ≥0), ∀ (s : Set E) (f : E → F),
      ApproximatesLinearOn f A s δ →
        (c : ℝ≥0∞) * volume s ≤ μHE[Module.finrank ℝ E] (f '' s) := by
  obtain ⟨K, _hKpos, hK⟩ := A.toLinearMap.injective_iff_antilipschitz.mp hA
  let j : ℝ≥0 := Real.toNNReal A.toLinearMap.normDet
  have hjc : c < j := by
    change (c : ℝ≥0∞) < j at hc
    exact ENNReal.coe_lt_coe.mp hc
  have hlim : Tendsto (fun δ : ℝ≥0 => (1 - δ * K) ^ Module.finrank ℝ E * j)
      (𝓝 0) (𝓝 j) := by
    simpa only [zero_mul, tsub_zero, one_pow, one_mul] using
      (show Continuous (fun δ : ℝ≥0 => (1 - δ * K) ^ Module.finrank ℝ E * j) by fun_prop).tendsto 0
  have hevent := (tendsto_order.1 hlim).1 c hjc
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝 0, δ * K < 1 := by
    have hlimK : Tendsto (fun δ : ℝ≥0 => δ * K) (𝓝 0) (𝓝 0) := by
      simpa only [id_eq, zero_mul] using (continuous_id.mul_const K).tendsto 0
    exact (tendsto_order.1 hlimK).2 1 zero_lt_one
  filter_upwards [hevent.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds] with δ hδ hδK s f hf
  have hcoef : (c : ℝ≥0∞) ≤ ((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
      ENNReal.ofReal A.toLinearMap.normDet := by
    change (c : ℝ≥0∞) ≤ ((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E * (j : ℝ≥0∞)
    exact_mod_cast hδ.le
  calc
    _ ≤ (((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        ENNReal.ofReal A.toLinearMap.normDet) * volume s := by gcongr
    _ = ((1 - δ * K : ℝ≥0) : ℝ≥0∞) ^ Module.finrank ℝ E *
        (ENNReal.ofReal A.toLinearMap.normDet * volume s) := by rw [mul_assoc]
    _ ≤ _ := approximation_euclidean_image_lower hA hK hf hδK

#print axioms euclidean_image_le_mul_of_normDet_lt
#print axioms mul_le_euclidean_image_of_lt_normDet
#assert_trust kernel euclidean_image_le_mul_of_normDet_lt
#assert_trust kernel mul_le_euclidean_image_of_lt_normDet

end NLA.TR06.Area
