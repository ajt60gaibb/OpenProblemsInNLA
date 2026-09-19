/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization by Codex agent /root/mi27_route_referee1.

Original problem: Audenaert and Kittaneh. Analytic resolution: Sidney Holden,
Flatiron Institute, Simons Foundation. This is the positive-pair normalization
used in that resolution. Strict trace positivity is proved from Mathlib's
positive-definite matrix theorem, with nonzero dimension derived from hn.
-/
import NLA.MI27.SpectralSemantics

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI27

/-- Positive trace normalization and exact reconstruction for one PD matrix. -/
lemma normalize_posdef {n : ℕ} [Nonempty (Fin n)] (A : Mat n) (hA : A.PosDef) :
    0 < trR A ∧ StrictDensity (((trR A : ℂ)⁻¹) • A) ∧
      A = (trR A : ℂ) • (((trR A : ℂ)⁻¹) • A) := by
  have ha : 0 < trR A := (Complex.pos_iff.mp hA.trace_pos).1
  have haC : (trR A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hinv : (0 : ℂ) < (trR A : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv]
    exact Complex.zero_lt_real.mpr (inv_pos.mpr ha)
  refine ⟨ha, ⟨hA.smul hinv, ?_⟩, ?_⟩
  · rw [Matrix.trace_smul, smul_eq_mul, trace_eq_ofReal_trR A hA.isHermitian,
      inv_mul_cancel₀ haC]
  · simp only [smul_smul, mul_inv_cancel₀ haC, one_smul]

/-- C03: no additional nonzero-trace or density hypotheses are required. -/
theorem normalize_positive_pair {n : ℕ} (hn : 1 ≤ n) (A B : Mat n)
    (hA : A.PosDef) (hB : B.PosDef) (htrace : Matrix.trace (A + B) = 1) :
    let a := trR A
    let b := trR B
    let ρ := ((a : ℂ)⁻¹) • A
    let σ := ((b : ℂ)⁻¹) • B
    0 < a ∧ 0 < b ∧ a + b = 1 ∧ StrictDensity ρ ∧ StrictDensity σ ∧
      A = (a : ℂ) • ρ ∧ B = (b : ℂ) • σ := by
  letI : Nonempty (Fin n) := ⟨⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩⟩
  dsimp only
  have hAn := normalize_posdef A hA
  have hBn := normalize_posdef B hB
  refine ⟨hAn.1, hBn.1, ?_, hAn.2.1, hBn.2.1, hAn.2.2, hBn.2.2⟩
  simpa only [Matrix.trace_add, Complex.add_re, Complex.one_re, trR] using
    congrArg Complex.re htrace

#print axioms normalize_positive_pair

end NLA.MI27
