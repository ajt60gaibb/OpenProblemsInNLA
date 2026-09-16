/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The deliberately coarse 1728 H^2 bound is proved by four rectangular entry
estimates and then the genuine six-dimensional Euclidean operator norm.
-/
import NLA.MF12.Gaps
import NLA.MF12.PowerBounds
import NLA.MF12.HolderBound
import NLA.MF12.Norms
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

lemma rectangular_entry_mul_bound {r k c : ℕ}
    (A : Matrix (Fin r) (Fin k) ℝ) (B : Matrix (Fin k) (Fin c) ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ i j, |A i j| ≤ a) (hB : ∀ i j, |B i j| ≤ b)
    (i : Fin r) (j : Fin c) : |(A * B) i j| ≤ (k : ℝ) * a * b := by
  rw [Matrix.mul_apply]
  calc
    |∑ s : Fin k, A i s * B s j| ≤ ∑ s : Fin k, |A i s * B s j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Fin k, a * b := by
      apply Finset.sum_le_sum
      intro s _
      rw [abs_mul]
      exact mul_le_mul (hA i s) (hB s j) (abs_nonneg _) ha
    _ = (k : ℝ) * a * b := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

lemma sourceV_entry_bound (r : Fin 6) (s : Fin 2) : |sourceV r s| ≤ 1 := by
  fin_cases r <;> fin_cases s
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(1 : ℝ)| ≤ 1
    norm_num

lemma sourceU_entry_bound (r : Fin 2) (s : Fin 6) : |sourceU r s| ≤ 1 := by
  fin_cases r <;> fin_cases s
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(-1 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(1 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(0 : ℝ)| ≤ 1
    norm_num
  · change |(1 : ℝ)| ≤ 1
    norm_num

lemma compressed_entry_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (qs : List ℕ) (r s : Fin 2) :
    |compressedProduct α qs r s| ≤ 1 + Real.rpow (qs.sum : ℝ) α := by
  have hD := diagonalBudget_bounds qs
  have hB := compressed_product_bound α hα hα1 qs
  have hR : 0 ≤ Real.rpow (qs.sum : ℝ) α := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [compressed_product_formula]
  fin_cases r <;> fin_cases s
  · change |diagonalBudget qs| ≤ _
    rw [abs_of_nonneg hD.1]
    linarith
  · change |offDiagonalBudget α qs| ≤ _
    rw [abs_of_nonneg hB.1]
    linarith
  · change |(0 : ℝ)| ≤ _
    rw [abs_zero]
    linarith
  · change |(1 : ℝ)| ≤ _
    rw [abs_one]
    linarith

lemma reset_factor_norm_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (q₀ qlast : ℕ) (B : Square 2) (E : ℝ) (hE : 0 ≤ E)
    (hB : ∀ i j, |B i j| ≤ E) :
    spectralNorm (fractionalMatrix α ^ qlast * sourceV * B *
      sourceU * fractionalMatrix α ^ q₀) ≤ 864 * fractionalPowerBound α ^ 2 * E := by
  let H := fractionalPowerBound α
  have hH : 0 ≤ H := (by norm_num : (0 : ℝ) ≤ 1).trans
    (fractionalPowerBound_ge_one α hα1)
  have hA (q : ℕ) (r s : Fin 6) : |(fractionalMatrix α ^ q) r s| ≤ H :=
    fractional_powers_entry_bound α hα hα1 q r s
  have hAV (i : Fin 6) (j : Fin 2) :
      |(fractionalMatrix α ^ qlast * sourceV) i j| ≤ 6 * H := by
    simpa only [Nat.cast_ofNat, mul_one] using
      rectangular_entry_mul_bound _ _ H 1 hH (by norm_num) (hA qlast) sourceV_entry_bound i j
  have hAVB (i : Fin 6) (j : Fin 2) :
      |(fractionalMatrix α ^ qlast * sourceV * B) i j| ≤ 12 * H * E := by
    have h := rectangular_entry_mul_bound _ _ (6 * H) E (by positivity) hE hAV hB i j
    exact h.trans_eq (by norm_num only [Nat.cast_ofNat]; ring)
  have hAVBU (i : Fin 6) (j : Fin 6) :
      |(fractionalMatrix α ^ qlast * sourceV * B * sourceU) i j| ≤ 24 * H * E := by
    have h := rectangular_entry_mul_bound _ _ (12 * H * E) 1 (by positivity) (by norm_num)
      hAVB sourceU_entry_bound i j
    exact h.trans_eq (by norm_num only [Nat.cast_ofNat]; ring)
  have hfull (i j : Fin 6) :
      |(fractionalMatrix α ^ qlast * sourceV * B * sourceU * fractionalMatrix α ^ q₀) i j| ≤
        144 * H ^ 2 * E := by
    have h := rectangular_entry_mul_bound _ _ (24 * H * E) H (by positivity) hH hAVBU (hA q₀) i j
    exact h.trans_eq (by norm_num only [Nat.cast_ofNat]; ring)
  have hnorm := spectralNorm_le_entry_bound _ (144 * H ^ 2 * E) (by positivity) hfull
  exact hnorm.trans_eq (by dsimp only [H]; norm_num only [Nat.cast_ofNat]; ring)

theorem fractional_all_word_upper (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (w : List Bool) (hw : 1 ≤ w.length) :
    spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix w) ≤
      fractionalUpper α * Real.rpow (w.length : ℝ) α := by
  have hH := fractionalPowerBound_ge_one α hα1
  have hR : 1 ≤ Real.rpow (w.length : ℝ) α :=
    Real.one_le_rpow (by exact_mod_cast hw) hα.le
  have hR0 : 0 ≤ Real.rpow (w.length : ℝ) α := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  obtain ⟨qs, hne, hword, hlength⟩ := gap_decomposition w
  cases qs with
  | nil => exact False.elim (hne rfl)
  | cons q₀ tail =>
      rcases List.eq_nil_or_concat' tail with hnil | ⟨mid, qlast, htail⟩
      · subst tail
        have hprod : binaryProduct (fractionalMatrix α) resetMatrix w = fractionalMatrix α ^ q₀ := by
          rw [← hword]
          simp only [gapWord_singleton, binaryProduct_replicate_false]
        have hbound := spectralNorm_le_entry_bound (fractionalMatrix α ^ q₀)
          (fractionalPowerBound α) (by linarith) (fractional_powers_entry_bound α hα hα1 q₀)
        have hconst : 6 * fractionalPowerBound α ≤ fractionalUpper α := by
          unfold fractionalUpper
          nlinarith [sq_nonneg (fractionalPowerBound α - 1)]
        have hC0 : 0 ≤ fractionalUpper α := by unfold fractionalUpper; positivity
        rw [hprod]
        calc
          spectralNorm (fractionalMatrix α ^ q₀) ≤ 6 * fractionalPowerBound α := by
            simpa only [Nat.cast_ofNat] using hbound
          _ ≤ fractionalUpper α := hconst
          _ ≤ fractionalUpper α * Real.rpow (w.length : ℝ) α := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hR hC0
      · subst tail
        have hmid : mid.sum ≤ w.length := by
          simp only [List.sum_cons, List.sum_append, List.sum_singleton,
            List.length_cons, List.length_append, List.length_singleton] at hlength
          omega
        have hmidpow : Real.rpow (mid.sum : ℝ) α ≤ Real.rpow (w.length : ℝ) α :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmid) hα.le
        have hB (i j : Fin 2) :
            |compressedProduct α mid i j| ≤ 2 * Real.rpow (w.length : ℝ) α :=
          (compressed_entry_bound α hα hα1 mid i j).trans (by linarith)
        have hprod : binaryProduct (fractionalMatrix α) resetMatrix w =
            fractionalMatrix α ^ qlast * sourceV * compressedProduct α mid *
              sourceU * fractionalMatrix α ^ q₀ := by
          rw [← hword]
          exact reset_product_factorization α q₀ qlast mid
        rw [hprod]
        calc
          _ ≤ 864 * fractionalPowerBound α ^ 2 * (2 * Real.rpow (w.length : ℝ) α) :=
            reset_factor_norm_bound α hα hα1 q₀ qlast (compressedProduct α mid) _
              (by positivity) hB
          _ = fractionalUpper α * Real.rpow (w.length : ℝ) α := by
            unfold fractionalUpper
            ring

#assert_trust kernel fractional_all_word_upper
#print axioms fractional_all_word_upper

end NLA.MF12
