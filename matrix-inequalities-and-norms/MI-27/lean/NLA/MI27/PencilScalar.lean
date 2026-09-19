/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The matrix-pencil weight comes
from Peter E. Frenkel's relative-entropy integral representation. These are
only its exact scalar count integrals; no matrix inertia or full C11 result
is assumed here. The seven exact headers and two transparent definitions
were reviewed by root and independent referee B before implementation.
See PENCIL-SCALAR-STATEMENTS.md. This author runs no Lean or Comparator.
-/
import NLA.MI27.Definitions
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
namespace NLA.MI27

def c11_pencilWeight (t : ℝ) : ℝ := 1 / (|t| * (t - 1) ^ 2)

def c11_pencilPrimitive (t : ℝ) : ℝ :=
  Real.log (1 + 1 / (t - 1)) - 1 / (t - 1)

lemma c11_pencilWeight_nonneg (t : ℝ) : 0 ≤ c11_pencilWeight t := by
  unfold c11_pencilWeight
  positivity

lemma c11_hasDerivAt_pencilPrimitive (t : ℝ) (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    HasDerivAt c11_pencilPrimitive (1 / (t * (t - 1) ^ 2)) t := by
  have ht : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  have harg : 1 + 1 / (t - 1) = t / (t - 1) := by
    field_simp [ht]
    <;> ring
  have harg0 : 1 + 1 / (t - 1) ≠ 0 := by
    rw [harg]
    exact div_ne_zero ht0 ht
  have hq : HasDerivAt (fun u : ℝ => 1 / (u - 1)) (-1 / (t - 1) ^ 2) t := by
    convert! (((hasDerivAt_id t).sub_const 1).inv ht) using 1
    ext u
    simp only [one_div, Pi.inv_apply, id_eq]
  have hd := (((hq.const_add 1).log harg0).sub hq)
  have he : (-1 / (t - 1) ^ 2) / (1 + 1 / (t - 1)) -
      (-1 / (t - 1) ^ 2) = 1 / (t * (t - 1) ^ 2) := by
    rw [harg]
    field_simp [ht0, ht]
    <;> ring
  convert! hd.congr_deriv he using 1

lemma c11_tendsto_pencilPrimitive :
    Filter.Tendsto c11_pencilPrimitive Filter.atTop (nhds 0) ∧
      Filter.Tendsto c11_pencilPrimitive Filter.atBot (nhds 0) := by
  have htop : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
    simpa only [sub_eq_add_neg, add_comm, id_eq] using
      tendsto_atTop_add_const_left atTop (-1 : ℝ) tendsto_id
  have hbot : Tendsto (fun t : ℝ => t - 1) atBot atBot := by
    simpa only [sub_eq_add_neg, add_comm, id_eq] using
      tendsto_atBot_add_const_left atBot (-1 : ℝ) tendsto_id
  have hqtop := htop.const_div_atTop (1 : ℝ)
  have hqbot := hbot.const_div_atBot (1 : ℝ)
  have hlogtop := ((tendsto_const_nhds (x := (1 : ℝ))).add hqtop).log (by norm_num)
  have hlogbot := ((tendsto_const_nhds (x := (1 : ℝ))).add hqbot).log (by norm_num)
  constructor
  · change Tendsto (fun t : ℝ => Real.log (1 + 1 / (t - 1)) - 1 / (t - 1)) atTop (𝓝 0)
    simpa only [add_zero, Real.log_one, sub_zero] using hlogtop.sub hqtop
  · change Tendsto (fun t : ℝ => Real.log (1 + 1 / (t - 1)) - 1 / (t - 1)) atBot (𝓝 0)
    simpa only [add_zero, Real.log_one, sub_zero] using hlogbot.sub hqbot

lemma c11_pencilWeight_integral_positive_tail (a : ℝ) (ha : 1 < a) :
    MeasureTheory.IntegrableOn c11_pencilWeight (Set.Ioi a) ∧
      (∫ t in Set.Ioi a, c11_pencilWeight t) = -c11_pencilPrimitive a := by
  have hd : ∀ t ∈ Ici a, HasDerivAt c11_pencilPrimitive (c11_pencilWeight t) t := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    simpa only [c11_pencilWeight, abs_of_pos ht0] using
      c11_hasDerivAt_pencilPrimitive t ht0.ne' (ne_of_gt ht1)
  have hp : ∀ t ∈ Ioi a, 0 ≤ c11_pencilWeight t := fun t _ => c11_pencilWeight_nonneg t
  have hi := integrableOn_Ioi_deriv_of_nonneg' hd hp c11_tendsto_pencilPrimitive.1
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi c11_tendsto_pencilPrimitive.1
  exact ⟨hi, by simpa only [zero_sub] using he⟩

lemma c11_pencilWeight_integral_negative_tail (a : ℝ) (ha : a < 0) :
    MeasureTheory.IntegrableOn c11_pencilWeight (Set.Iio a) ∧
      (∫ t in Set.Iio a, c11_pencilWeight t) = -c11_pencilPrimitive a := by
  have hd : ∀ t ∈ Ici (-a),
      HasDerivAt (fun u : ℝ => c11_pencilPrimitive (-u)) (c11_pencilWeight (-t)) t := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le (neg_pos.mpr ha) ht
    have hneg : -t < 0 := neg_neg_of_pos htpos
    have hd₀ := c11_hasDerivAt_pencilPrimitive (-t) (ne_of_lt hneg) (by linarith)
    have hd₁ := hd₀.comp t (hasDerivAt_neg' t)
    have he : (1 / ((-t) * ((-t) - 1) ^ 2)) * (-1) = c11_pencilWeight (-t) := by
      unfold c11_pencilWeight
      rw [abs_of_neg hneg]
      field_simp
      <;> ring
    convert! hd₁.congr_deriv he using 1
  have hp : ∀ t ∈ Ioi (-a), 0 ≤ c11_pencilWeight (-t) :=
    fun t _ => c11_pencilWeight_nonneg (-t)
  have hlim : Tendsto (fun t : ℝ => c11_pencilPrimitive (-t)) atTop (𝓝 0) :=
    c11_tendsto_pencilPrimitive.2.comp tendsto_neg_atTop_atBot
  have hir := integrableOn_Ioi_deriv_of_nonneg' hd hp hlim
  have her := integral_Ioi_of_hasDerivAt_of_tendsto' hd hir hlim
  have hpre : (fun t : ℝ => -t) ⁻¹' Iio a = Ioi (-a) := by
    ext t
    simp only [mem_preimage, mem_Iio, mem_Ioi]
    constructor <;> intro h <;> linarith
  have hi : IntegrableOn c11_pencilWeight (Iio a) := by
    apply (MeasurePreserving.integrableOn_comp_preimage
      (Measure.measurePreserving_neg (volume : Measure ℝ))
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    simpa only [hpre, Function.comp_def] using hir
  refine ⟨hi, ?_⟩
  have hreflect : (∫ t in Ioi (-a), c11_pencilWeight (-t)) =
      ∫ t in Iio a, c11_pencilWeight t := by
    simpa only [neg_neg, integral_Iic_eq_integral_Iio] using
      integral_comp_neg_Ioi (-a) c11_pencilWeight
  rw [hreflect] at her
  simpa only [neg_neg, zero_sub] using her

lemma c11_pencilPrimitive_at_threshold (c : ℝ) (hc : -1 < c) (hc0 : c ≠ 0) :
    -c11_pencilPrimitive (-1 / c) = Real.log (1 + c) - c / (1 + c) := by
  have hcpos : 0 < 1 + c := by linarith
  have hq : 1 / (-1 / c - 1) = -c / (1 + c) := by
    have he : -1 / c - 1 = -(1 + c) / c := by
      field_simp [hc0]
      <;> ring
    rw [he]
    field_simp [hc0, hcpos.ne']
    <;> ring
  have harg : 1 + -c / (1 + c) = 1 / (1 + c) := by
    field_simp [hcpos.ne']
    <;> ring
  unfold c11_pencilPrimitive
  rw [hq, harg, Real.log_div one_ne_zero hcpos.ne', Real.log_one]
  ring

lemma c11_scalar_pencil_count_integral (c : ℝ) (hc : -1 < c) :
    MeasureTheory.Integrable
      (fun t : ℝ => c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) ∧
      (∫ t : ℝ, c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) =
        Real.log (1 + c) - c / (1 + c) := by
  by_cases hc0 : c = 0
  · subst c
    have hnot : ¬ (1 : ℝ) < 0 := not_lt_of_ge zero_le_one
    simp only [mul_zero, add_zero, if_neg hnot, Real.log_one, zero_div, sub_zero,
      integral_zero, and_self]
    refine ⟨?_, trivial⟩
    convert! (integrable_zero ℝ ℝ volume : Integrable (0 : ℝ → ℝ) volume) using 1 <;> rfl
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · have ha : 1 < -1 / c := (lt_div_iff_of_neg hcneg).2 (by linarith)
    have hfun :
        (fun t : ℝ => c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) =
          (Ioi (-1 / c)).indicator c11_pencilWeight := by
      funext t
      have hlt : 1 + t * c < 0 ↔ -1 / c < t := by
        rw [div_lt_iff_of_neg hcneg]
        constructor <;> intro h <;> linarith
      simp only [Set.indicator_apply, Set.mem_Ioi, hlt]
      split_ifs <;> simp
    obtain ⟨hi, he⟩ := c11_pencilWeight_integral_positive_tail (-1 / c) ha
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hi.integrable_indicator measurableSet_Ioi
    · rw [hfun, integral_indicator measurableSet_Ioi, he]
      exact c11_pencilPrimitive_at_threshold c hc hc0
  · have ha : -1 / c < 0 := div_neg_of_neg_of_pos (by norm_num) hcpos
    have hfun :
        (fun t : ℝ => c11_pencilWeight t * (if 1 + t * c < 0 then (1 : ℝ) else 0)) =
          (Iio (-1 / c)).indicator c11_pencilWeight := by
      funext t
      have hlt : 1 + t * c < 0 ↔ t < -1 / c := by
        rw [lt_div_iff₀ hcpos]
        constructor <;> intro h <;> linarith
      simp only [Set.indicator_apply, Set.mem_Iio, hlt]
      split_ifs <;> simp
    obtain ⟨hi, he⟩ := c11_pencilWeight_integral_negative_tail (-1 / c) ha
    refine ⟨?_, ?_⟩
    · rw [hfun]
      exact hi.integrable_indicator measurableSet_Iio
    · rw [hfun, integral_indicator measurableSet_Iio, he]
      exact c11_pencilPrimitive_at_threshold c hc hc0

#print axioms c11_pencilWeight_nonneg
#assert_trust kernel c11_pencilWeight_nonneg
#print axioms c11_hasDerivAt_pencilPrimitive
#assert_trust kernel c11_hasDerivAt_pencilPrimitive
#print axioms c11_tendsto_pencilPrimitive
#assert_trust kernel c11_tendsto_pencilPrimitive
#print axioms c11_pencilWeight_integral_positive_tail
#assert_trust kernel c11_pencilWeight_integral_positive_tail
#print axioms c11_pencilWeight_integral_negative_tail
#assert_trust kernel c11_pencilWeight_integral_negative_tail
#print axioms c11_pencilPrimitive_at_threshold
#assert_trust kernel c11_pencilPrimitive_at_threshold
#print axioms c11_scalar_pencil_count_integral
#assert_trust kernel c11_scalar_pencil_count_integral

end NLA.MI27
