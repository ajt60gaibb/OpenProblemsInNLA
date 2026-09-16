/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge.
-/
import NLA.IE14.Basic
import NLA.IE14.Certificates
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
namespace NLA.IE14

theorem half_complex_ne_zero : (1/2 : ℂ) ≠ 0 := by
  have he : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num [norm_div]
  apply norm_pos_iff.mp
  rw [he]
  exact half_bounds_certificate.1

theorem norm_half_complex_le_one : ‖(1/2 : ℂ)‖ ≤ 1 := by
  have he : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by norm_num [norm_div]
  rw [he]
  exact half_bounds_certificate.2

theorem lower_diag (n : ℕ) (i : Fin n) : witnessLower n i i = 1 := by
  simp [witnessLower]

theorem lower_triangular (n : ℕ) : (witnessLower n).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  have hne : i ≠ j := ne_of_lt hij
  have h1 : ¬ j.val+1=i.val := by omega
  have h2 : ¬ j.val+2=i.val := by omega
  simp [witnessLower, hne, h1, h2]

theorem lower_norm (n : ℕ) (i j : Fin n) : ‖witnessLower n i j‖ ≤ 1 := by
  unfold witnessLower
  split_ifs <;> norm_num

theorem upper_triangular (n : ℕ) : (witnessUpper n).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  have hlast : ¬ j.val+1=n := by omega
  have hne : i ≠ j := ne_of_gt hji
  have h0 : ¬ (i.val=0 ∧ j.val=1) := by omega
  simp [witnessUpper, hlast, hne, h0]

theorem upper_diag_ne_zero (n : ℕ) (i : Fin n) : witnessUpper n i i ≠ 0 := by
  unfold witnessUpper
  by_cases hi : i.val+1=n
  · simp only [hi, ↓reduceIte]
    exact_mod_cast (Nat.succ_ne_zero (Nat.fib (n+1)))
  · simp only [hi, ↓reduceIte]
    split_ifs
    · exact half_complex_ne_zero
    · exact one_ne_zero

theorem factors_det_ne_zero (n : ℕ) : (witnessLower n * witnessUpper n).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_of_isLowerTriangular _ (lower_triangular n),
    Matrix.det_of_isUpperTriangular (upper_triangular n)]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [lower_diag]
    exact one_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ => upper_diag_ne_zero n i)

theorem factorIndex_injective (n : ℕ) (hn : 4 ≤ n) : Function.Injective (factorIndex n hn) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [factorIndex] at hv
  split_ifs at hv <;> simp only at hv <;> omega

def factorEquiv (n : ℕ) (hn : 4 ≤ n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (factorIndex n hn) ⟨factorIndex_injective n hn,
    Finite.surjective_of_injective (factorIndex_injective n hn)⟩

theorem witness_det_ne_zero (n : ℕ) (hn : 4 ≤ n) : (witnessMatrix n hn).det ≠ 0 := by
  change ((witnessLower n * witnessUpper n).submatrix (factorEquiv n hn) id).det ≠ 0
  rw [Matrix.det_permute]
  apply mul_ne_zero _ (factors_det_ne_zero n)
  exact_mod_cast (Units.ne_zero (Equiv.Perm.sign (factorEquiv n hn)))

end NLA.IE14
