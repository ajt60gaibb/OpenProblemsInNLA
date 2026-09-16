/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The fixed finite identities below are explicit scalar certificates. Lean checks
every conversion from an actual matrix entry before proving its ring identity.
-/
import NLA.MF12.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

namespace NLA.MF12

lemma source_uv : sourceU * sourceV = (1 : Square 2) := by
  ext r s
  fin_cases r <;> fin_cases s
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_six]
  · change (1 * 1 + (-1) * 0 + 0 * 1 + 1 * 0 + 0 * 0 + 0 * 0 : ℝ) = 1
    norm_num
  · change (1 * 0 + (-1) * 0 + 0 * 0 + 1 * 0 + 0 * 1 + 0 * 1 : ℝ) = 0
    norm_num
  · change (0 * 1 + 0 * 0 + 0 * 1 + 0 * 0 + 0 * 0 + 1 * 0 : ℝ) = 0
    norm_num
  · change (0 * 0 + 0 * 0 + 0 * 0 + 0 * 0 + 0 * 1 + 1 * 1 : ℝ) = 1
    norm_num

theorem fractional_projection (α : ℝ) :
    sourceU * sourceV = (1 : Square 2) ∧ resetMatrix ^ 2 = resetMatrix ∧
    fractionalMatrix α ≠ resetMatrix := by
  refine ⟨source_uv, ?_, ?_⟩
  · calc
      resetMatrix ^ 2 = (sourceV * sourceU) * (sourceV * sourceU) := by
        rw [pow_two]; rfl
      _ = sourceV * (sourceU * sourceV) * sourceU := by simp only [Matrix.mul_assoc]
      _ = resetMatrix := by rw [source_uv, Matrix.mul_one]; rfl
  · intro he
    have h := congrArg (fun B : Square 6 => B 0 1) he
    change fractionalMatrix α 0 1 = (sourceV * sourceU) 0 1 at h
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    change (0 : ℝ) = 1 * (-1) + 0 * 0 at h
    norm_num at h

theorem jordan_two_power (t : ℝ) (q : ℕ) :
    jordanTwo t ^ q = t ^ q • (!![1, (q : ℝ); 0, 1] : Square 2) := by
  induction q with
  | zero =>
      ext r s
      fin_cases r <;> fin_cases s <;>
        norm_num [Matrix.smul_apply, Matrix.one_apply]
  | succ q ih =>
      rw [pow_succ, ih]
      ext r s
      fin_cases r <;> fin_cases s <;>
        simp only [Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.smul_apply, smul_eq_mul]
      all_goals
        dsimp [jordanTwo]
        simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

/-- The explicit powers of the unchanged 1+2+2+1 source matrix. -/
def fractionalPowerForm (α : ℝ) (q : ℕ) : Square 6 :=
  !![1, 0, 0, 0, 0, 0;
     0, baseLambda ^ q, (q : ℝ) * baseLambda ^ q, 0, 0, 0;
     0, 0, baseLambda ^ q, 0, 0, 0;
     0, 0, 0, baseMu α ^ q, (q : ℝ) * baseMu α ^ q, 0;
     0, 0, 0, 0, baseMu α ^ q, 0;
     0, 0, 0, 0, 0, 1]

lemma fractionalPowerForm_zero (α : ℝ) : fractionalPowerForm α 0 = 1 := by
  ext r s
  fin_cases r <;> fin_cases s
  · change (1 : ℝ) = 1
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (baseLambda ^ (0) : ℝ) = 1
    norm_num
  · change (((0 : ℕ) : ℝ) * baseLambda ^ (0) : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (baseLambda ^ (0) : ℝ) = 1
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (baseMu α ^ (0) : ℝ) = 1
    norm_num
  · change (((0 : ℕ) : ℝ) * baseMu α ^ (0) : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (baseMu α ^ (0) : ℝ) = 1
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (0 : ℝ) = 0
    norm_num
  · change (1 : ℝ) = 1
    norm_num

lemma fractionalPowerForm_mul (α : ℝ) (q : ℕ) :
    fractionalPowerForm α q * fractionalMatrix α = fractionalPowerForm α (q + 1) := by
  ext r s
  fin_cases r <;> fin_cases s
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_six]
  · change ((1) * (1) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 1
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((1) * (0) + (0) * (baseLambda) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((1) * (0) + (0) * (baseLambda) + (0) * (baseLambda) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((1) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((1) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (0) * (baseMu α) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((1) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (1) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (1) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (baseLambda) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = baseLambda ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (baseLambda) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (baseLambda) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = ((q + 1 : ℕ) : ℝ) * baseLambda ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (baseMu α) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (baseMu α) + (0) * (baseMu α) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (1) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (1) + (0) * (0) + (baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (baseLambda ^ (q)) * (baseLambda) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = baseLambda ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (baseLambda ^ (q)) * (0) + (0) * (baseMu α) + (0) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (baseLambda ^ (q)) * (0) + (0) * (baseMu α) + (0) * (baseMu α) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (0) + (0) * (1) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (1) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (0) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (baseLambda) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (baseMu α) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = baseMu α ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (baseMu α) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (baseMu α) + (0) * (0) : ℝ) = ((q + 1 : ℕ) : ℝ) * baseMu α ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (1) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (1) + (0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (baseLambda) + (0) * (0) + (baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (baseMu α ^ (q)) * (baseMu α) + (0) * (0) : ℝ) = baseMu α ^ (q + 1)
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (0) * (1) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (1) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (1) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (0) + (0) * (0) + (0) * (0) + (1) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (baseLambda) + (0) * (baseLambda) + (0) * (0) + (0) * (0) + (1) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (0) * (0) + (1) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (baseMu α) + (0) * (baseMu α) + (1) * (0) : ℝ) = 0
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (1) * (1) : ℝ) = 1
    simp only [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

lemma fractionalMatrix_power (α : ℝ) (q : ℕ) :
    fractionalMatrix α ^ q = fractionalPowerForm α q := by
  induction q with
  | zero => simpa only [pow_zero] using (fractionalPowerForm_zero α).symm
  | succ q ih => rw [pow_succ, ih, fractionalPowerForm_mul]

def fractionalPowerV (α : ℝ) (q : ℕ) : Matrix (Fin 6) (Fin 2) ℝ :=
  !![1, 0; (q : ℝ) * baseLambda ^ q, 0; baseLambda ^ q, 0;
     0, (q : ℝ) * baseMu α ^ q; 0, baseMu α ^ q; 0, 1]

lemma fractionalPowerForm_mul_V (α : ℝ) (q : ℕ) :
    fractionalPowerForm α q * sourceV = fractionalPowerV α q := by
  ext r s
  fin_cases r <;> fin_cases s
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_six]
  · change ((1) * (1) + (0) * (0) + (0) * (1) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = 1
    ring
  · change ((1) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (1) + (0) * (1) : ℝ) = 0
    ring
  · change ((0) * (1) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (1) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = (q : ℝ) * baseLambda ^ q
    ring
  · change ((0) * (0) + (baseLambda ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (1) + (0) * (1) : ℝ) = 0
    ring
  · change ((0) * (1) + (0) * (0) + (baseLambda ^ (q)) * (1) + (0) * (0) + (0) * (0) + (0) * (0) : ℝ) = baseLambda ^ q
    ring
  · change ((0) * (0) + (0) * (0) + (baseLambda ^ (q)) * (0) + (0) * (0) + (0) * (1) + (0) * (1) : ℝ) = 0
    ring
  · change ((0) * (1) + (0) * (0) + (0) * (1) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (0) + (((q : ℕ) : ℝ) * baseMu α ^ (q)) * (1) + (0) * (1) : ℝ) = (q : ℝ) * baseMu α ^ q
    ring
  · change ((0) * (1) + (0) * (0) + (0) * (1) + (0) * (0) + (baseMu α ^ (q)) * (0) + (0) * (0) : ℝ) = 0
    ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (baseMu α ^ (q)) * (1) + (0) * (1) : ℝ) = baseMu α ^ q
    ring
  · change ((0) * (1) + (0) * (0) + (0) * (1) + (0) * (0) + (0) * (0) + (1) * (0) : ℝ) = 0
    ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * (0) + (0) * (1) + (1) * (1) : ℝ) = 1
    ring

theorem compressed_powers (α : ℝ) (q : ℕ) :
    compressed α q = !![1 - loss q, gain α q; 0, 1] := by
  rw [compressed, fractionalMatrix_power, Matrix.mul_assoc, fractionalPowerForm_mul_V]
  ext r s
  fin_cases r <;> fin_cases s
  all_goals simp only [Matrix.mul_apply, Fin.sum_univ_six]
  · change ((1) * (1) + (-1) * ((q : ℝ) * baseLambda ^ q) + (0) * (baseLambda ^ q) + (1) * (0) + (0) * (0) + (0) * (0) : ℝ) = 1 - (q : ℝ) * baseLambda ^ q
    ring
  · change ((1) * (0) + (-1) * (0) + (0) * (0) + (1) * ((q : ℝ) * baseMu α ^ q) + (0) * (baseMu α ^ q) + (0) * (1) : ℝ) = (q : ℝ) * baseMu α ^ q
    ring
  · change ((0) * (1) + (0) * ((q : ℝ) * baseLambda ^ q) + (0) * (baseLambda ^ q) + (0) * (0) + (0) * (0) + (1) * (0) : ℝ) = 0
    ring
  · change ((0) * (0) + (0) * (0) + (0) * (0) + (0) * ((q : ℝ) * baseMu α ^ q) + (0) * (baseMu α ^ q) + (1) * (1) : ℝ) = 1
    ring

#assert_trust kernel fractional_projection
#assert_trust kernel jordan_two_power
#assert_trust kernel compressed_powers
#print axioms fractional_projection
#print axioms jordan_two_power
#print axioms compressed_powers

end NLA.MF12
