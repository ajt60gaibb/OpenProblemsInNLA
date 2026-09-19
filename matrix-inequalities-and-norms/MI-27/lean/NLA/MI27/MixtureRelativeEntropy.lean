/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

Finite-mixture form of the relative-entropy identity in Sidney Holden's MI27
solution. Frenkel and Hirche--Tomamichel retain the integral-identity credit.
The full noncommuting C11 identity is a proved import. Each mixture term is
truncated at its own exact cutoff before substitution. This exact header was
reviewed by two other agents before bodies; see PREBODY-FREEZE.json.
-/
import NLA.MI27.RelativeEntropyHockeyStick
import NLA.MI27.MixtureBasics
import NLA.MI27.MixtureChangeVariables
import NLA.MI27.MixturePositivePart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c12_relative_entropy_mixture_finite {n : ℕ} (hn : 1 ≤ n) (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    IntervalIntegrable
      (fun γ : ℝ => b ^ 2 * E γ ρ σ / (γ * (b + a * γ) ^ 2) +
        b ^ 2 * E γ σ ρ / (a + b * γ) ^ 2) MeasureTheory.volume 1 R ∧
      relEntropy ρ ((a : ℂ) • ρ + (b : ℂ) • σ) =
        ∫ γ in (1 : ℝ)..R,
          b ^ 2 * E γ ρ σ / (γ * (b + a * γ) ^ 2) +
          b ^ 2 * E γ σ ρ / (a + b * γ) ^ 2 := by
  let M : Mat n := (a : ℂ) • ρ + (b : ℂ) • σ
  let L : ℝ := R / (b + a * R)
  let U : ℝ := a + b * R
  have hM : StrictDensity M := c12_mixture_strict_density ρ σ hρ hσ a b ha hb hab
  obtain ⟨hL1, hLR, hU1, hUR, hlow, hupp⟩ :=
    c12_mixture_cutoffs ρ σ hρ hσ R hR hρσ hσρ a b ha hb hab
  have hρM : ρ ≤ (R : ℂ) • M :=
    hlow.trans (smul_le_smul_of_nonneg_right
      (show ((L : ℝ) : ℂ) ≤ (R : ℂ) by exact_mod_cast hLR) hM.1.posSemidef.nonneg)
  have hMρ : M ≤ (R : ℂ) • ρ :=
    hupp.trans (smul_le_smul_of_nonneg_right
      (show ((U : ℝ) : ℂ) ≤ (R : ℂ) by exact_mod_cast hUR) hρ.1.posSemidef.nonneg)
  have hbase := relative_entropy_finite_hockey_stick hn ρ M hρ hM R hR hρM hMρ
  let f : ℝ → ℝ := fun v => E v ρ M / v
  let g : ℝ → ℝ := fun v => E v M ρ / v ^ 2
  have hp (v : ℝ) (hv : 1 ≤ v) : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hf : ContinuousOn f (Set.Icc (1 : ℝ) R) :=
    (hockey_stick_continuous_gamma hn ρ M hρ.1.isHermitian hM.1.isHermitian).continuousOn.div
      continuousOn_id (fun v hv => (hp v hv.1).ne')
  have hg : ContinuousOn g (Set.Icc (1 : ℝ) R) :=
    (hockey_stick_continuous_gamma hn M ρ hM.1.isHermitian hρ.1.isHermitian).continuousOn.div
      (continuousOn_id.pow 2) (fun v hv => pow_ne_zero 2 (hp v hv.1).ne')
  have hfi : IntervalIntegrable f volume 1 R := hf.intervalIntegrable_of_Icc hR
  have hgi : IntervalIntegrable g volume 1 R := hg.intervalIntegrable_of_Icc hR
  have hfzero (v : ℝ) (hv : L ≤ v) : f v = 0 := by
    dsimp only [f]
    rw [c11_hockey_stick_zero_tail ρ M hρ.1.isHermitian hM.1.posSemidef L v hlow hv,
      zero_div]
  have hgzero (v : ℝ) (hv : U ≤ v) : g v = 0 := by
    dsimp only [g]
    rw [c11_hockey_stick_zero_tail M ρ hM.1.isHermitian hρ.1.posSemidef U v hupp hv,
      zero_div]
  have hfcut := c12_integral_truncate_zero_tail f L R hL1 hLR hf hfzero
  have hgcut := c12_integral_truncate_zero_tail g U R hU1 hUR hg hgzero
  have hfL : ContinuousOn f (Set.Icc (1 : ℝ) L) :=
    hf.mono (fun _ hv => ⟨hv.1, hv.2.trans hLR⟩)
  have hgU : ContinuousOn g (Set.Icc (1 : ℝ) U) :=
    hg.mono (fun _ hv => ⟨hv.1, hv.2.trans hUR⟩)
  have hfchange := c12_change_variable_forward f a b R ha hb hab hR hfL
  have hgchange := c12_change_variable_reverse g a b R hb hab hR hgU
  have hd1 (v : ℝ) (hv : 1 ≤ v) : 0 < b + a * v := add_pos hb (mul_pos ha (hp v hv))
  have hd2 (v : ℝ) (hv : 1 ≤ v) : 0 < a + b * v := add_pos ha (mul_pos hb (hp v hv))
  have hfpoint (v : ℝ) (hv : 1 ≤ v) :
      f (v / (b + a * v)) * (b / (b + a * v) ^ 2) =
        b ^ 2 * E v ρ σ / (v * (b + a * v) ^ 2) := by
    dsimp only [f, M]
    rw [c12_E_mixture_forward ρ σ hρ.1.isHermitian hσ.1.isHermitian a b v ha hb hv]
    field_simp [(hd1 v hv).ne', (hp v hv).ne']
    <;> ring
  have hgpoint (v : ℝ) :
      g (a + b * v) * b = b ^ 2 * E v σ ρ / (a + b * v) ^ 2 := by
    dsimp only [g, M]
    rw [c12_E_mixture_reverse ρ σ hρ.1.isHermitian hσ.1.isHermitian a b v hb.le]
    ring
  have hfint : (∫ v in (1 : ℝ)..R, f v) =
      ∫ v in (1 : ℝ)..R, b ^ 2 * E v ρ σ / (v * (b + a * v) ^ 2) := by
    calc
      _ = ∫ v in (1 : ℝ)..L, f v := hfcut
      _ = ∫ v in (1 : ℝ)..R, f (v / (b + a * v)) * (b / (b + a * v) ^ 2) := hfchange
      _ = _ := intervalIntegral.integral_congr (fun v hv => hfpoint v (Set.uIcc_of_le hR ▸ hv).1)
  have hgint : (∫ v in (1 : ℝ)..R, g v) =
      ∫ v in (1 : ℝ)..R, b ^ 2 * E v σ ρ / (a + b * v) ^ 2 := by
    calc
      _ = ∫ v in (1 : ℝ)..U, g v := hgcut
      _ = ∫ v in (1 : ℝ)..R, g (a + b * v) * b := hgchange
      _ = _ := intervalIntegral.integral_congr (fun v _ => hgpoint v)
  have hE1 : ContinuousOn (fun v : ℝ => E v ρ σ) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn ρ σ hρ.1.isHermitian hσ.1.isHermitian).continuousOn
  have hE2 : ContinuousOn (fun v : ℝ => E v σ ρ) (Set.Icc 1 R) :=
    (hockey_stick_continuous_gamma hn σ ρ hσ.1.isHermitian hρ.1.isHermitian).continuousOn
  have hi1 : IntervalIntegrable
      (fun v : ℝ => b ^ 2 * E v ρ σ / (v * (b + a * v) ^ 2)) volume 1 R := by
    refine ContinuousOn.intervalIntegrable_of_Icc hR ?_
    exact (continuousOn_const.mul hE1).div
      (continuousOn_id.mul ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2))
      (fun v hv => mul_ne_zero (hp v hv.1).ne' (pow_ne_zero 2 (hd1 v hv.1).ne'))
  have hi2 : IntervalIntegrable
      (fun v : ℝ => b ^ 2 * E v σ ρ / (a + b * v) ^ 2) volume 1 R := by
    refine ContinuousOn.intervalIntegrable_of_Icc hR ?_
    exact (continuousOn_const.mul hE2).div
      ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
      (fun v hv => pow_ne_zero 2 (hd2 v hv.1).ne')
  refine ⟨hi1.add hi2, ?_⟩
  calc
    relEntropy ρ M = ∫ v in (1 : ℝ)..R, f v + g v := hbase.2
    _ = (∫ v in (1 : ℝ)..R, f v) + ∫ v in (1 : ℝ)..R, g v :=
      intervalIntegral.integral_add hfi hgi
    _ = (∫ v in (1 : ℝ)..R, b ^ 2 * E v ρ σ / (v * (b + a * v) ^ 2)) +
        ∫ v in (1 : ℝ)..R, b ^ 2 * E v σ ρ / (a + b * v) ^ 2 := by rw [hfint, hgint]
    _ = _ := (intervalIntegral.integral_add hi1 hi2).symm

#print axioms c12_relative_entropy_mixture_finite
#assert_trust kernel c12_relative_entropy_mixture_finite

end NLA.MI27
