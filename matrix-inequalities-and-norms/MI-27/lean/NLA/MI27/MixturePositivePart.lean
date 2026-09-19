/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

Two exact positive-part identities in Sidney Holden's MI27 entropy argument.
Both headers were reviewed by two other agents before bodies, recorded in
PREBODY-FREEZE.json. The imported positive-part homogeneity and its earlier
matrix/CFC authorship are retained. No commuting-matrix hypothesis is used.
-/
import NLA.MI27.HockeyStickSubstitution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c12_E_mixture_forward {n : ℕ} (ρ σ : Mat n)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 1 ≤ γ) :
    E (γ / (b + a * γ)) ρ ((a : ℂ) • ρ + (b : ℂ) • σ) =
      (b / (b + a * γ)) * E γ ρ σ := by
  have hd : 0 < b + a * γ :=
    add_pos hb (mul_pos ha (lt_of_lt_of_le zero_lt_one hγ))
  have hdC : (b : ℂ) + (a : ℂ) * (γ : ℂ) ≠ 0 := by
    exact_mod_cast hd.ne'
  have hlin : ρ - ((γ / (b + a * γ) : ℝ) : ℂ) •
      ((a : ℂ) • ρ + (b : ℂ) • σ) =
      ((b / (b + a * γ) : ℝ) : ℂ) • (ρ - (γ : ℂ) • σ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul]
    field_simp [hdC]
    <;> ring
  have hdiff : (ρ - (γ : ℂ) • σ).IsHermitian :=
    hρ.sub (hσ.smul (by simp [IsSelfAdjoint]))
  unfold E
  rw [hlin, c11_tracePos_smul_nonneg _ hdiff _ (div_nonneg hb.le hd.le)]

lemma c12_E_mixture_reverse {n : ℕ} (ρ σ : Mat n)
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (a b γ : ℝ) (hb : 0 ≤ b) :
    E (a + b * γ) ((a : ℂ) • ρ + (b : ℂ) • σ) ρ = b * E γ σ ρ := by
  have hlin : (a : ℂ) • ρ + (b : ℂ) • σ - ((a + b * γ : ℝ) : ℂ) • ρ =
      (b : ℂ) • (σ - (γ : ℂ) • ρ) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  have hdiff : (σ - (γ : ℂ) • ρ).IsHermitian :=
    hσ.sub (hρ.smul (by simp [IsSelfAdjoint]))
  unfold E
  rw [hlin, c11_tracePos_smul_nonneg _ hdiff b hb]

#print axioms c12_E_mixture_forward
#assert_trust kernel c12_E_mixture_forward
#print axioms c12_E_mixture_reverse
#assert_trust kernel c12_E_mixture_reverse

end NLA.MI27
