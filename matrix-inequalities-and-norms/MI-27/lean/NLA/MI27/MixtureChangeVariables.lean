/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

Exact finite substitutions in Sidney Holden's MI27 entropy argument.
The three headers were independently approved before bodies, as recorded in
PREBODY-FREEZE.json. All integrals use finite original cutoffs; R=1 is retained.
Mathlib's exact interval substitution theorem replaces numerical quadrature.
-/
import NLA.MI27.Definitions
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
noncomputable section
namespace NLA.MI27

lemma c12_integral_truncate_zero_tail (f : ℝ → ℝ) (L R : ℝ)
    (hL : 1 ≤ L) (hLR : L ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) R))
    (hzero : ∀ v : ℝ, L ≤ v → f v = 0) :
    (∫ v in (1 : ℝ)..R, f v) = ∫ v in (1 : ℝ)..L, f v := by
  have h1L : IntervalIntegrable f volume 1 L :=
    (hf.mono (fun _ hx => ⟨hx.1, hx.2.trans hLR⟩)).intervalIntegrable_of_Icc hL
  have hLRi : IntervalIntegrable f volume L R :=
    (hf.mono (fun _ hx => ⟨hL.trans hx.1, hx.2⟩)).intervalIntegrable_of_Icc hLR
  have hz : (∫ v in L..R, f v) = 0 := by
    calc
      (∫ v in L..R, f v) = ∫ _v in L..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact hzero v ((Set.uIcc_of_le hLR ▸ hv).1)
      _ = 0 := by simp only [intervalIntegral.integral_zero]
  simpa only [hz, add_zero] using
    (intervalIntegral.integral_add_adjacent_intervals h1L hLRi).symm

lemma c12_change_variable_forward (f : ℝ → ℝ) (a b R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hR : 1 ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) (R / (b + a * R)))) :
    (∫ v in (1 : ℝ)..(R / (b + a * R)), f v) =
      ∫ γ in (1 : ℝ)..R, f (γ / (b + a * γ)) * (b / (b + a * γ) ^ 2) := by
  have hd (x : ℝ) (hx : 1 ≤ x) : 0 < b + a * x :=
    add_pos hb (mul_pos ha (lt_of_lt_of_le zero_lt_one hx))
  have hmap (x : ℝ) (hx : x ∈ Set.uIcc (1 : ℝ) R) :
      x / (b + a * x) ∈ Set.Icc (1 : ℝ) (R / (b + a * R)) := by
    have hx' : x ∈ Set.Icc (1 : ℝ) R := Set.uIcc_of_le hR ▸ hx
    refine ⟨(le_div_iff₀ (hd x hx'.1)).2 ?_,
      (div_le_div_iff₀ (hd x hx'.1) (hd R hR)).2 ?_⟩
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hx'.1)]
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hx'.2)]
  have hder : ∀ x ∈ Set.uIcc (1 : ℝ) R,
      HasDerivAt (fun x : ℝ => x / (b + a * x)) (b / (b + a * x) ^ 2) x := by
    intro x hx
    have hx' : 1 ≤ x := (Set.uIcc_of_le hR ▸ hx).1
    have hh := (hasDerivAt_id x).div
      (((hasDerivAt_id x).const_mul a).const_add b) (hd x hx').ne'
    convert! hh using 1 <;> try rfl
    dsimp only [id] <;> ring
  have hcont : ContinuousOn (fun x : ℝ => b / (b + a * x) ^ 2)
      (Set.uIcc (1 : ℝ) R) := by
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
    intro x hx
    exact pow_ne_zero 2 (hd x (Set.uIcc_of_le hR ▸ hx).1).ne'
  have hfimage : ContinuousOn f
      ((fun x : ℝ => x / (b + a * x)) '' Set.uIcc (1 : ℝ) R) := by
    apply hf.mono
    rintro _ ⟨x, hx, rfl⟩
    exact hmap x hx
  have hh := intervalIntegral.integral_comp_mul_deriv' hder hcont hfimage
  have hba : b + a = 1 := by linarith
  simpa only [Function.comp_def, mul_one, hba, div_one] using hh.symm

lemma c12_change_variable_reverse (f : ℝ → ℝ) (a b R : ℝ)
    (hb : 0 < b) (hab : a + b = 1) (hR : 1 ≤ R)
    (hf : ContinuousOn f (Set.Icc (1 : ℝ) (a + b * R))) :
    (∫ v in (1 : ℝ)..(a + b * R), f v) =
      ∫ γ in (1 : ℝ)..R, f (a + b * γ) * b := by
  have hder : ∀ x ∈ Set.uIcc (1 : ℝ) R,
      HasDerivAt (fun x : ℝ => a + b * x) b x := by
    intro x _
    convert! (((hasDerivAt_id x).const_mul b).const_add a) using 1 <;>
      simp only [id_eq, mul_one] <;> rfl
  have hfimage : ContinuousOn f
      ((fun x : ℝ => a + b * x) '' Set.uIcc (1 : ℝ) R) := by
    apply hf.mono
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Icc (1 : ℝ) R := Set.uIcc_of_le hR ▸ hx
    constructor
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hx'.1)]
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hx'.2)]
  have hh := intervalIntegral.integral_comp_mul_deriv' hder continuousOn_const hfimage
  simpa only [Function.comp_def, mul_one, hab] using hh.symm

#print axioms c12_integral_truncate_zero_tail
#assert_trust kernel c12_integral_truncate_zero_tail
#print axioms c12_change_variable_forward
#assert_trust kernel c12_change_variable_forward
#print axioms c12_change_variable_reverse
#assert_trust kernel c12_change_variable_reverse

end NLA.MI27
