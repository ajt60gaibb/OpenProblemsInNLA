/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
The fixed dimension factors avoid an unnecessary singular-value tensor theorem.
-/
import NLA.MF12.Words
import NLA.MF12.Norms
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical

namespace NLA.MF12

lemma tensor_apply {d e : ℕ} (A : Square d) (B : Square e) (r s : Fin (d * e)) :
    tensor A B r s =
      A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm s).1 *
        B (finProdFinEquiv.symm r).2 (finProdFinEquiv.symm s).2 := rfl

lemma tensor_pair_apply {d e : ℕ} (A : Square d) (B : Square e)
    (r s : Fin d) (i j : Fin e) :
    tensor A B (finProdFinEquiv (r, i)) (finProdFinEquiv (s, j)) = A r s * B i j := by
  simp only [tensor_apply, Equiv.symm_apply_apply]

lemma tensor_mul {d e : ℕ} (A C : Square d) (B D : Square e) :
    tensor A B * tensor C D = tensor (A * C) (B * D) := by
  unfold tensor
  rw [Matrix.submatrix_mul_equiv, ← Matrix.mul_kronecker_mul]

@[simp] lemma tensor_one (d e : ℕ) : tensor (1 : Square d) (1 : Square e) = 1 := by
  unfold tensor
  rw [Matrix.one_kronecker_one, Matrix.submatrix_one_equiv]

theorem tensor_word_identity {d e : ℕ} (A P : Square d) (J : Square e)
    (w : List Bool) :
    binaryProduct (tensor A J) (tensor P J) w =
      tensor (binaryProduct A P w) (J ^ w.length) := by
  induction w with
  | nil => simp
  | cons b w ih =>
      rw [binaryProduct_cons, ih, binaryProduct_cons, List.length_cons, pow_succ]
      cases b <;> simp only [cond_false, cond_true, tensor_mul]

lemma entryMax_tensor (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (A : Square d) (B : Square e) : entryMax (tensor A B) = entryMax A * entryMax B := by
  apply le_antisymm
  · apply entryMax_le_of_entry_bound _ _ (mul_nonneg (entryMax_nonneg A) (entryMax_nonneg B))
    intro r s
    rw [tensor_apply, abs_mul]
    exact mul_le_mul (abs_entry_le_entryMax A _ _) (abs_entry_le_entryMax B _ _)
      (abs_nonneg _) (entryMax_nonneg A)
  · obtain ⟨r, s, hA⟩ := entryMax_attained d hd A
    obtain ⟨i, j, hB⟩ := entryMax_attained e he B
    have h := abs_entry_le_entryMax (tensor A B)
      (finProdFinEquiv (r, i)) (finProdFinEquiv (s, j))
    simpa only [tensor_pair_apply, abs_mul, hA, hB] using h

theorem tensor_norm_comparison (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (A : Square d) (B : Square e) :
    entryMax (tensor A B) = entryMax A * entryMax B ∧
    spectralNorm A * spectralNorm B / ((d : ℝ) * (e : ℝ)) ≤ spectralNorm (tensor A B) ∧
    spectralNorm (tensor A B) ≤ ((d : ℝ) * (e : ℝ)) * spectralNorm A * spectralNorm B := by
  have hA := entry_maximum_norm_comparison d hd A
  have hB := entry_maximum_norm_comparison e he B
  have hde : 1 ≤ d * e := Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (by omega) (by omega))
  have hT := entry_maximum_norm_comparison (d * e) hde (tensor A B)
  have hentry := entryMax_tensor d e hd he A B
  have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
  have heR : 0 < (e : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one he
  have hdim : 0 < (d : ℝ) * (e : ℝ) := mul_pos hdR heR
  refine ⟨hentry, ?_, ?_⟩
  · apply (div_le_iff₀ hdim).mpr
    have hprod := mul_le_mul hA.2.2.2.2 hB.2.2.2.2 (spectralNorm_nonneg B)
      (mul_nonneg (Nat.cast_nonneg d) (entryMax_nonneg A))
    calc
      spectralNorm A * spectralNorm B ≤
          ((d : ℝ) * (e : ℝ)) * (entryMax A * entryMax B) := by
            convert hprod using 1 <;> ring
      _ = ((d : ℝ) * (e : ℝ)) * entryMax (tensor A B) := by rw [hentry]
      _ ≤ ((d : ℝ) * (e : ℝ)) * spectralNorm (tensor A B) :=
        mul_le_mul_of_nonneg_left hT.2.2.2.1 hdim.le
      _ = spectralNorm (tensor A B) * ((d : ℝ) * (e : ℝ)) := mul_comm _ _
  · have hprod := mul_le_mul hA.2.2.2.1 hB.2.2.2.1 (entryMax_nonneg B)
      (spectralNorm_nonneg A)
    calc
      spectralNorm (tensor A B) ≤ ((d * e : ℕ) : ℝ) * entryMax (tensor A B) := hT.2.2.2.2
      _ = ((d : ℝ) * (e : ℝ)) * (entryMax A * entryMax B) := by rw [Nat.cast_mul, hentry]
      _ ≤ ((d : ℝ) * (e : ℝ)) * (spectralNorm A * spectralNorm B) :=
        mul_le_mul_of_nonneg_left hprod hdim.le
      _ = ((d : ℝ) * (e : ℝ)) * spectralNorm A * spectralNorm B := by ring

#assert_trust kernel tensor_norm_comparison
#assert_trust kernel tensor_word_identity
#print axioms tensor_norm_comparison
#print axioms tensor_word_identity

end NLA.MF12
