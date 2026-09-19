/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/nr04_mf14_final_referee_a.

Original MI27 question: Audenaert and Kittaneh. Analytic resolution: Sidney
Holden, Flatiron Institute, Simons Foundation. The imported normalization,
entropy derivative and finite-time integral bounds retain their credits.

Exact frozen C19, recorded in STATEMENTS.md before this body. The actual
derivative is bounded by the finite-time estimate at zero; no derivative
or entropy identity appears as an added premise. This source author runs
no Lean or Comparator. Root performs serial verification.
-/
import NLA.MI27.EntropyTrajectory
import NLA.MI27.Normalization
import NLA.MI27.EntropyDerivative
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open MeasureTheory Filter
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator Topology
noncomputable section
namespace NLA.MI27

theorem logarithmic_commutator_dual_bound {n : ℕ} (hn : 1 ≤ n) (A B H : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (htrace : Matrix.trace (A + B) = 1)
    (hH : H.IsHermitian) :
    let a := trR A
    let b := trR B
    let K := (-Complex.I) • comm B (logM (A + B))
    0 ≤ h a b ∧ |trR (H * K)| ≤ opNorm H * h a b := by
  let a := trR A
  let b := trR B
  let ρ : Mat n := ((a : ℂ)⁻¹) • A
  let σ : Mat n := ((b : ℂ)⁻¹) • B
  obtain ⟨ha, hb, hab, hρ, hσ, hAeq, hBeq⟩ :=
    normalize_positive_pair hn A B hA hB htrace
  change 0 < a at ha
  change 0 < b at hb
  change a + b = 1 at hab
  change StrictDensity ρ at hρ
  change StrictDensity σ at hσ
  change A = (a : ℂ) • ρ at hAeq
  change B = (b : ℂ) • σ at hBeq
  have hh : 0 ≤ h a b := by
    have hm := (kernel_entropy_mass_bound a b 1 ha hb hab le_rfl).2.2.2.2
    simpa only [intervalIntegral.integral_same, add_zero] using hm
  have hfinite (t : ℝ) :
      |entropy (A + conjFlow H B t) - entropy (A + B)| ≤
        |t| * opNorm H * h a b := by
    have he := entropy_trajectory_lipschitz hn ρ σ H hρ hσ hH a b ha hb hab t
    have hflow : conjFlow H B t = (b : ℂ) • conjFlow H σ t := by
      rw [hBeq]
      simp only [conjFlow, mul_smul_comm, smul_mul_assoc]
    calc
      |entropy (A + conjFlow H B t) - entropy (A + B)| =
          |entropy ((a : ℂ) • ρ + (b : ℂ) • conjFlow H σ t) -
            entropy ((a : ℂ) • ρ + (b : ℂ) • σ)| := by rw [hflow, ← hAeq, ← hBeq]
      _ ≤ |t| * opNorm H * h a b := he
  have hd := entropy_unitary_mix_derivative hn A B H hA hB hH
  have hc : 0 ≤ opNorm H * h a b := mul_nonneg (norm_nonneg _) hh
  have hdb := hd.le_of_lip' hc (show ∀ᶠ t : ℝ in 𝓝 0,
      ‖entropy (A + conjFlow H B t) - entropy (A + conjFlow H B 0)‖ ≤
        (opNorm H * h a b) * ‖t - 0‖ from by
    filter_upwards with t
    calc
      ‖entropy (A + conjFlow H B t) - entropy (A + conjFlow H B 0)‖ =
          |entropy (A + conjFlow H B t) - entropy (A + B)| := by
        simp only [Real.norm_eq_abs, conjFlow, flow_zero, Matrix.conjTranspose_one,
          one_mul, mul_one]
      _ ≤ |t| * opNorm H * h a b := hfinite t
      _ = (opNorm H * h a b) * ‖t - 0‖ := by rw [Real.norm_eq_abs, sub_zero]; ring)
  refine ⟨hh, ?_⟩
  simpa only [Real.norm_eq_abs] using hdb

#print axioms logarithmic_commutator_dual_bound
#assert_trust kernel logarithmic_commutator_dual_bound

end NLA.MI27
