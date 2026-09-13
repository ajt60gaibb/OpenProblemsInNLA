/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: George Stepaniants

Exact finite variance and positive-square decomposition from Colbrook's MI-03
argument. Formalization: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA. AI-assisted.
-/
import NLA.MI03.Modulus
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem pairVariance_identity {n k : ℕ} (A : Fin k → Mat n) :
    pairVariance A = (k : ℂ) • (∑ j, (A j).conjTranspose * A j) -
      (summandSum A).conjTranspose * summandSum A := by
  simp only [pairVariance, Matrix.conjTranspose_sub, sub_mul, mul_sub,
    ← Finset.smul_sum, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Finset.mul_sum, ← Finset.sum_mul, ← Matrix.conjTranspose_sum,
    summandSum]
  simp only [← Nat.cast_smul_eq_nsmul ℂ]
  module

theorem pairVariance_posSemidef {n k : ℕ} (A : Fin k → Mat n) :
    (pairVariance A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  apply Matrix.posSemidef_sum
  intro j _
  exact (Matrix.posSemidef_conjTranspose_mul_self (A i - A j)).smul
    (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 1 / 2)

theorem shiftedSquare_posSemidef {n k : ℕ} (A : Fin k → Mat n) :
    (shiftedSquare A).PosSemidef := by
  have h : (matrixModulus (summandSum A) -
      ((k : ℂ) / 2) • (1 : Mat n)).IsHermitian :=
    (modulus_nonneg (summandSum A)).isHermitian.sub
      (Matrix.PosSemidef.one.smul (by positivity : (0 : ℂ) ≤ (k : ℂ) / 2)).isHermitian
  have hp := Matrix.posSemidef_conjTranspose_mul_self
    (matrixModulus (summandSum A) - ((k : ℂ) / 2) • (1 : Mat n))
  simpa only [h.eq, ← pow_two, shiftedSquare] using hp

theorem positive_decomposition_proved {n k : ℕ} (_hn : 1 ≤ n) (_hk : 2 ≤ k)
    (A : Fin k → Mat n) :
    (k : ℂ) • errorGap A ((k : ℝ) / 4) =
      (k : ℂ) • (∑ j, (matrixModulus (A j) -
        matrixModulus (A j) * matrixModulus (A j))) +
        pairVariance A + shiftedSquare A ∧
    (pairVariance A).PosSemidef ∧ (shiftedSquare A).PosSemidef := by
  refine ⟨?_, pairVariance_posSemidef A, shiftedSquare_posSemidef A⟩
  rw [pairVariance_identity]
  simp only [shiftedSquare, pow_two, sub_mul, mul_sub,
    smul_mul_assoc, mul_smul_comm, mul_one, one_mul,
    modulus_square, Finset.sum_sub_distrib, errorGap, modulusSum,
    Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  module

theorem universal_upper_bound_proved (k : ℕ) (hk : 2 ≤ k) :
    AdmissibleConstant k ((k : ℝ) / 4) := by
  refine ⟨by positivity, ?_⟩
  intro n hn A hA
  have hs : (∑ j, (matrixModulus (A j) -
      matrixModulus (A j) * matrixModulus (A j))).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro j _
    exact (contraction_modulus_proved hn (A j) (hA j)).2
  have hpos := (hs.smul (by positivity : (0 : ℂ) ≤ (k : ℂ))).add
    (pairVariance_posSemidef A) |>.add (shiftedSquare_posSemidef A)
  rw [← (positive_decomposition_proved hn hk A).1] at hpos
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hout := hpos.smul (by positivity : (0 : ℂ) ≤ (k : ℂ)⁻¹)
  simpa only [smul_smul, inv_mul_cancel₀ hk0, one_smul] using hout

end NLA.MI03
