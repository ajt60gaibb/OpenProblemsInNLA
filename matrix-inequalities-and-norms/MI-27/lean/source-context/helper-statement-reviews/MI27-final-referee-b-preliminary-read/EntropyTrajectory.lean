/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. Imported spectral, relative-
entropy, finite-kernel and flow proofs retain their mathematical/code credits.

Exact frozen C15, recorded again in STATEMENTS.md before this body. One
uniform cutoff is used at both times. Only finite hockey-stick differences
are integrated; no derivative of a positive-part integral is taken. C12 is
an imported proved theorem, with no extra hypothesis or temporary axiom.
This author runs no Lean or Comparator; root performs serial verification.
-/
import NLA.MI27.WeightedEntropy
import NLA.MI27.HockeyStickFlow
import NLA.MI27.UniformCutoff
import NLA.MI27.KernelIntegrals
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

theorem entropy_trajectory_lipschitz {n : ℕ} (hn : 1 ≤ n) (ρ σ H : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (hH : H.IsHermitian)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (t : ℝ) :
    |entropy ((a : ℂ) • ρ + (b : ℂ) • conjFlow H σ t) -
        entropy ((a : ℂ) • ρ + (b : ℂ) • σ)| ≤
      |t| * opNorm H * h a b := by
  obtain ⟨R, hR, hcut⟩ := uniform_hockey_stick_cutoff hn ρ σ hρ hσ
  have hcutTime (u : ℝ) :
      ρ ≤ (R : ℂ) • conjFlow H σ u ∧ conjFlow H σ u ≤ (R : ℂ) • ρ := by
    let U : unitary (Mat n) := ⟨flow H u, flow_mem_unitary H hH u⟩
    exact ⟨(hcut U).1, (hcut U).2.1⟩
  have hzero : conjFlow H σ 0 = σ := by
    simp only [conjFlow, flow_zero, Matrix.conjTranspose_one, one_mul, mul_one]
  have hcut0 := hcutTime 0
  rw [hzero] at hcut0
  have hσt : StrictDensity (conjFlow H σ t) := by
    have hs := (unitary_flow_semantics hn H hH).2.2.2 σ t
    exact ⟨hs.2.2.1 hσ.1, hs.2.2.2.1.trans hσ.2⟩
  have hentropy : entropy (conjFlow H σ t) = entropy σ :=
    ((unitary_flow_semantics hn H hH).2.2.2 σ t).2.2.2.2.2.1 hσ.1.isHermitian
  obtain ⟨hti, htval⟩ := weighted_entropy_finite_kernel hn ρ (conjFlow H σ t)
    hρ hσt R hR.le (hcutTime t).1 (hcutTime t).2 a b ha hb hab
  obtain ⟨h0i, h0val⟩ := weighted_entropy_finite_kernel hn ρ σ hρ hσ R hR.le
    hcut0.1 hcut0.2 a b ha hb hab
  have hchi :
      entropy ((a : ℂ) • ρ + (b : ℂ) • conjFlow H σ t) -
          entropy ((a : ℂ) • ρ + (b : ℂ) • σ) =
        chi a b ρ (conjFlow H σ t) - chi a b ρ σ := by
    simp only [chi, hentropy]
    ring
  let C : ℝ := |t| * opNorm H
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg t) (norm_nonneg _)
  have hk := kernel_integrals a b R ha hb hab hR.le
  have hbi : IntervalIntegrable
      (fun γ : ℝ => (kernelAB a b γ + kernelBA a b γ) * C) volume 1 R :=
    (hk.1.add hk.2.1).mul_const C
  have hpoint (γ : ℝ) (hγ : γ ∈ Set.Ioc (1 : ℝ) R) :
      ‖(kernelAB a b γ * E γ ρ (conjFlow H σ t) +
          kernelBA a b γ * E γ (conjFlow H σ t) ρ) -
        (kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ)‖ ≤
        (kernelAB a b γ + kernelBA a b γ) * C := by
    have hγp : 0 < γ := lt_trans zero_lt_one hγ.1
    have hka : 0 ≤ kernelAB a b γ :=
      (div_pos (mul_pos ha hb) (mul_pos hγp (add_pos hb (mul_pos ha hγp)))).le
    have hkb : 0 ≤ kernelBA a b γ :=
      (div_pos (mul_pos ha hb) (mul_pos hγp (add_pos ha (mul_pos hb hγp)))).le
    have hdiff := hockey_stick_unitary_lipschitz hn ρ σ H hρ hσ hH γ 0 t hγ.1.le
    simp only [hzero, sub_zero] at hdiff
    have halg :
        (kernelAB a b γ * E γ ρ (conjFlow H σ t) +
            kernelBA a b γ * E γ (conjFlow H σ t) ρ) -
          (kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ) =
        kernelAB a b γ * (E γ ρ (conjFlow H σ t) - E γ ρ σ) +
          kernelBA a b γ * (E γ (conjFlow H σ t) ρ - E γ σ ρ) := by ring
    rw [Real.norm_eq_abs, halg]
    calc
      |kernelAB a b γ * (E γ ρ (conjFlow H σ t) - E γ ρ σ) +
          kernelBA a b γ * (E γ (conjFlow H σ t) ρ - E γ σ ρ)| ≤
          |kernelAB a b γ * (E γ ρ (conjFlow H σ t) - E γ ρ σ)| +
            |kernelBA a b γ * (E γ (conjFlow H σ t) ρ - E γ σ ρ)| := abs_add_le _ _
      _ = kernelAB a b γ * |E γ ρ (conjFlow H σ t) - E γ ρ σ| +
          kernelBA a b γ * |E γ (conjFlow H σ t) ρ - E γ σ ρ| := by
        rw [abs_mul, abs_of_nonneg hka, abs_mul, abs_of_nonneg hkb]
      _ ≤ kernelAB a b γ * C + kernelBA a b γ * C :=
        add_le_add (mul_le_mul_of_nonneg_left hdiff.1 hka)
          (mul_le_mul_of_nonneg_left hdiff.2 hkb)
      _ = (kernelAB a b γ + kernelBA a b γ) * C := by ring
  have hib := intervalIntegral.norm_integral_le_of_norm_le hR.le
    (Filter.Eventually.of_forall hpoint) hbi
  have hmass := (kernel_entropy_mass_bound a b R ha hb hab hR.le).2.2.2.2
  rw [hchi, htval, h0val, ← intervalIntegral.integral_sub hti h0i]
  calc
    |∫ γ in (1 : ℝ)..R,
        (kernelAB a b γ * E γ ρ (conjFlow H σ t) +
          kernelBA a b γ * E γ (conjFlow H σ t) ρ) -
        (kernelAB a b γ * E γ ρ σ + kernelBA a b γ * E γ σ ρ)| ≤
        ((∫ γ in (1 : ℝ)..R, kernelAB a b γ) +
          ∫ γ in (1 : ℝ)..R, kernelBA a b γ) * C := by
      simpa only [Real.norm_eq_abs, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_add hk.1 hk.2.1] using hib
    _ ≤ h a b * C := mul_le_mul_of_nonneg_right hmass hC
    _ = |t| * opNorm H * h a b := by dsimp only [C]; ring

#print axioms entropy_trajectory_lipschitz
#assert_trust kernel entropy_trajectory_lipschitz

end NLA.MI27
