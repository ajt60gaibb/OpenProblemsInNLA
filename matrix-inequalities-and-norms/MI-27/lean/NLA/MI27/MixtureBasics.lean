/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root.

Original MI27 question: Audenaert and Kittaneh. Analytic solution: Sidney Holden,
Flatiron Institute, Simons Foundation. Integral representation: Frenkel and
Hirche--Tomamichel. Imported matrix/CFC sources retain their original credits.
The three exact helper headers below were reviewed by two other agents before
bodies; see this packet's PREBODY-FREEZE.json. Full C12 is not claimed here.
-/
import NLA.MI27.FiniteHockeyStick
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

lemma c12_mixture_strict_density {n : ℕ} (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    StrictDensity ((a : ℂ) • ρ + (b : ℂ) • σ) := by
  refine ⟨(hρ.1.smul (Complex.zero_lt_real.mpr ha)).add
    (hσ.1.smul (Complex.zero_lt_real.mpr hb)), ?_⟩
  simp only [Matrix.trace_add, Matrix.trace_smul, hρ.2, hσ.2,
    smul_eq_mul, mul_one, ← Complex.ofReal_add, hab, Complex.ofReal_one]

lemma c12_chi_relative_entropy {n : ℕ} (ρ σ : Mat n) (a b : ℝ) :
    chi a b ρ σ =
      a * relEntropy ρ ((a : ℂ) • ρ + (b : ℂ) • σ) +
      b * relEntropy σ ((a : ℂ) • ρ + (b : ℂ) • σ) := by
  unfold chi entropy relEntropy trR
  simp only [mul_sub, add_mul, smul_mul_assoc, Matrix.trace_sub, Matrix.trace_add,
    Matrix.trace_smul, Complex.sub_re, Complex.add_re, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

lemma c12_mixture_cutoffs {n : ℕ} (ρ σ : Mat n)
    (hρ : StrictDensity ρ) (hσ : StrictDensity σ) (R : ℝ) (hR : 1 ≤ R)
    (hρσ : ρ ≤ (R : ℂ) • σ) (hσρ : σ ≤ (R : ℂ) • ρ)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    1 ≤ R / (b + a * R) ∧ R / (b + a * R) ≤ R ∧
      1 ≤ a + b * R ∧ a + b * R ≤ R ∧
      ρ ≤ ((R / (b + a * R) : ℝ) : ℂ) • ((a : ℂ) • ρ + (b : ℂ) • σ) ∧
      (a : ℂ) • ρ + (b : ℂ) • σ ≤ ((a + b * R : ℝ) : ℂ) • ρ := by
  have hRp : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hd : 0 < b + a * R := add_pos hb (mul_pos ha hRp)
  have hd1 : 1 ≤ b + a * R := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hR)]
  have hdR : b + a * R ≤ R := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hR)]
  have hL1 : 1 ≤ R / (b + a * R) := (le_div_iff₀ hd).2 (by simpa using hdR)
  have hLR : R / (b + a * R) ≤ R := (div_le_iff₀ hd).2 (by
    nlinarith [mul_nonneg hRp.le (sub_nonneg.mpr hd1)])
  have hU1 : 1 ≤ a + b * R := by nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hR)]
  have hUR : a + b * R ≤ R := by nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hR)]
  have hbC : (0 : ℂ) ≤ (b : ℂ) := Complex.zero_le_real.mpr hb.le
  have hs1 : (b : ℂ) • ρ ≤ (b : ℂ) • ((R : ℂ) • σ) :=
    smul_le_smul_of_nonneg_left hρσ hbC
  have hs2 : (b : ℂ) • σ ≤ (b : ℂ) • ((R : ℂ) • ρ) :=
    smul_le_smul_of_nonneg_left hσρ hbC
  have hforward : ((b + a * R : ℝ) : ℂ) • ρ ≤
      (R : ℂ) • ((a : ℂ) • ρ + (b : ℂ) • σ) := by
    calc
      ((b + a * R : ℝ) : ℂ) • ρ =
          (a : ℂ) • ((R : ℂ) • ρ) + (b : ℂ) • ρ := by
        simp only [Complex.ofReal_add, Complex.ofReal_mul, add_smul, smul_smul]
        exact add_comm _ _
      _ ≤ (a : ℂ) • ((R : ℂ) • ρ) + (b : ℂ) • ((R : ℂ) • σ) :=
        add_le_add le_rfl hs1
      _ = (R : ℂ) • ((a : ℂ) • ρ + (b : ℂ) • σ) := by
        simp only [smul_add, smul_smul, mul_comm]
  have hdC : ((b + a * R : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hinvC : (0 : ℂ) ≤ (((b + a * R : ℝ) : ℂ)⁻¹) := by
    rw [← Complex.ofReal_inv]
    exact Complex.zero_le_real.mpr (inv_nonneg.mpr hd.le)
  have hlow : ρ ≤ ((R / (b + a * R) : ℝ) : ℂ) •
      ((a : ℂ) • ρ + (b : ℂ) • σ) := by
    have hh := smul_le_smul_of_nonneg_left hforward hinvC
    have hc : (((b + a * R : ℝ) : ℂ)⁻¹) * (R : ℂ) =
        ((R / (b + a * R) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div, div_eq_mul_inv]
      exact mul_comm _ _
    simpa only [smul_smul, inv_mul_cancel₀ hdC, one_smul, hc] using hh
  have hupp : (a : ℂ) • ρ + (b : ℂ) • σ ≤ ((a + b * R : ℝ) : ℂ) • ρ := by
    calc
      (a : ℂ) • ρ + (b : ℂ) • σ ≤
          (a : ℂ) • ρ + (b : ℂ) • ((R : ℂ) • ρ) :=
        add_le_add le_rfl hs2
      _ = ((a + b * R : ℝ) : ℂ) • ρ := by
        simp only [Complex.ofReal_add, Complex.ofReal_mul, add_smul, smul_smul]
  exact ⟨hL1, hLR, hU1, hUR, hlow, hupp⟩

#print axioms c12_mixture_strict_density
#assert_trust kernel c12_mixture_strict_density
#print axioms c12_chi_relative_entropy
#assert_trust kernel c12_chi_relative_entropy
#print axioms c12_mixture_cutoffs
#assert_trust kernel c12_mixture_cutoffs

end NLA.MI27
