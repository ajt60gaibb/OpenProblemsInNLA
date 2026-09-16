/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
Every lifted word is an actual Kronecker product with a Jordan power.
The two factors remain distinct, including the zero integer-exponent case.
-/
import NLA.MF12.Lower
import NLA.MF12.JordanBounds
import NLA.MF12.Tensor
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Classical

namespace NLA.MF12

lemma tensor_left_injective_of_entry_one {d e : ℕ} (B : Square e)
    (i j : Fin e) (hB : B i j = 1) :
    Function.Injective (fun A : Square d => tensor A B) := by
  intro A C hAC
  ext r s
  have h := congrArg (fun D : Square (d * e) =>
    D (finProdFinEquiv (r, i)) (finProdFinEquiv (s, j))) hAC
  simpa only [tensor_pair_apply, hB, mul_one] using h

lemma lifted_distinct (α : ℝ) (m : ℕ) : liftedA α m ≠ liftedP m := by
  have hJ : jordanMatrix m (0 : Fin (m + 1)) 0 = 1 := by
    simpa only [pow_one] using jordan_power_diagonal m 1 0
  exact fun he => (fractional_projection α).2.2
    (tensor_left_injective_of_entry_one (jordanMatrix m) 0 0 hJ he)

lemma liftedLower_pos (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (m : ℕ) :
    0 < liftedLower α m := by
  exact div_pos (mul_pos (fractional_parameters α hα hα1).2.2.2.2.1
    (jordanLower_pos m)) (by positivity)

lemma lifted_growth_bounds (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (m n : ℕ)
    (hn : 1 ≤ n) :
    liftedLower α m * Real.rpow (n : ℝ) (α + (m : ℝ)) ≤
      familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ∧
    familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ≤
      liftedUpper α m * Real.rpow (n : ℝ) (α + (m : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdim : 0 < (6 : ℝ) * ((m + 1 : ℕ) : ℝ) := by positivity
  have hJ := (jordan_growth_estimates m).2.2 n hn
  have hpar := fractional_parameters α hα hα1
  have hC : 0 < fractionalUpper α := lt_of_lt_of_le hpar.2.2.2.2.1 hpar.2.2.2.2.2
  constructor
  · let w := lowerWord n
    have hw : w.length = n := (lower_word_exact α n).1
    have hword : binaryProduct (liftedA α m) (liftedP m) w =
        tensor (binaryProduct (fractionalMatrix α) resetMatrix w) (jordanMatrix m ^ n) := by
      unfold liftedA liftedP
      rw [tensor_word_identity, hw]
    have hT := tensor_norm_comparison 6 (m + 1) (by omega) (by omega)
      (binaryProduct (fractionalMatrix α) resetMatrix w) (jordanMatrix m ^ n)
    have hprod := mul_le_mul (fractional_lower_all_lengths α hα hα1 n hn) hJ.1
      (mul_nonneg (jordanLower_pos m).le (pow_nonneg hnR.le m))
      (spectralNorm_nonneg (binaryProduct (fractionalMatrix α) resetMatrix w))
    calc
      liftedLower α m * Real.rpow (n : ℝ) (α + (m : ℝ)) =
          (fractionalLower α * Real.rpow (n : ℝ) α *
            (jordanLower m * (n : ℝ) ^ m)) / (6 * ((m + 1 : ℕ) : ℝ)) := by
              simp only [liftedLower, Real.rpow_eq_pow]
              rw [Real.rpow_add hnR, Real.rpow_natCast]
              ring
      _ ≤ (spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix w) *
          spectralNorm (jordanMatrix m ^ n)) / (6 * ((m + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hprod hdim.le
      _ ≤ spectralNorm (tensor (binaryProduct (fractionalMatrix α) resetMatrix w)
          (jordanMatrix m ^ n)) := by simpa only [Nat.cast_ofNat] using hT.2.1
      _ = spectralNorm (binaryProduct (liftedA α m) (liftedP m) w) := congrArg spectralNorm hword.symm
      _ ≤ familyGrowth (pairFamily (liftedA α m) (liftedP m)) n := by
        simpa only [hw] using binaryProduct_le_familyGrowth (liftedA α m) (liftedP m) w
  · apply familyGrowth_le_of_binary
    intro w hw
    have hword : binaryProduct (liftedA α m) (liftedP m) w =
        tensor (binaryProduct (fractionalMatrix α) resetMatrix w) (jordanMatrix m ^ n) := by
      unfold liftedA liftedP
      rw [tensor_word_identity, hw]
    have hT := tensor_norm_comparison 6 (m + 1) (by omega) (by omega)
      (binaryProduct (fractionalMatrix α) resetMatrix w) (jordanMatrix m ^ n)
    have hF : spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix w) ≤
        fractionalUpper α * Real.rpow (n : ℝ) α := by
      simpa only [hw] using fractional_all_word_upper α hα hα1 w (by omega)
    have hprod := mul_le_mul hF hJ.2 (spectralNorm_nonneg (jordanMatrix m ^ n))
      (mul_nonneg hC.le (Real.rpow_nonneg hnR.le _))
    calc
      spectralNorm (binaryProduct (liftedA α m) (liftedP m) w) =
          spectralNorm (tensor (binaryProduct (fractionalMatrix α) resetMatrix w)
            (jordanMatrix m ^ n)) := congrArg spectralNorm hword
      _ ≤ (6 * ((m + 1 : ℕ) : ℝ)) *
          (spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix w) *
            spectralNorm (jordanMatrix m ^ n)) := by
              exact hT.2.2.trans_eq (by norm_num only [Nat.cast_ofNat]; ring)
      _ ≤ (6 * ((m + 1 : ℕ) : ℝ)) *
          (fractionalUpper α * Real.rpow (n : ℝ) α *
            (((m + 1 : ℕ) : ℝ) * (n : ℝ) ^ m)) :=
        mul_le_mul_of_nonneg_left hprod hdim.le
      _ = liftedUpper α m * Real.rpow (n : ℝ) (α + (m : ℝ)) := by
        simp only [liftedUpper, Real.rpow_eq_pow]
        rw [Real.rpow_add hnR, Real.rpow_natCast]
        ring

theorem fractional_tensor_growth (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (m : ℕ) :
    liftedA α m ≠ liftedP m ∧ 0 < liftedLower α m ∧ liftedLower α m ≤ liftedUpper α m ∧
    ∀ n : ℕ, 1 ≤ n →
      liftedLower α m * Real.rpow (n : ℝ) (α + (m : ℝ)) ≤
        familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ∧
      familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ≤
        liftedUpper α m * Real.rpow (n : ℝ) (α + (m : ℝ)) := by
  have hbounds := lifted_growth_bounds α hα hα1 m
  have h1 := hbounds 1 le_rfl
  have hcompare := h1.1.trans h1.2
  refine ⟨lifted_distinct α m, liftedLower_pos α hα hα1 m, ?_, hbounds⟩
  simpa only [Nat.cast_one, Real.rpow_eq_pow, Real.one_rpow, mul_one] using hcompare

#assert_trust kernel fractional_tensor_growth
#print axioms fractional_tensor_growth

end NLA.MF12
