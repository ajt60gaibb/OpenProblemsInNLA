/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact rational matrix identities for Colbrook's IE-23 resolution, using the
Dokmanić–Gribonval example. The genuine inverse and rank are derived from
matrix products, rather than defined by their proposed values. AI-assisted
formalization, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE23.Norms

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

lemma witness_gram : witnessA * witnessA.conjTranspose = witnessGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessGram, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_gram_mul_inv : witnessGram * witnessGramInv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessGram, witnessGramInv, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_inv_mul_gram : witnessGramInv * witnessGram = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessGram, witnessGramInv, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_gram_isUnit : IsUnit witnessGram := by
  exact ⟨⟨witnessGram, witnessGramInv, witness_gram_mul_inv, witness_inv_mul_gram⟩, rfl⟩

lemma witness_gram_inverse : witnessGram⁻¹ = witnessGramInv :=
  Matrix.inv_eq_left_inv witness_inv_mul_gram

lemma witness_moorePenrose : moorePenrose witnessA = witnessB := by
  unfold moorePenrose
  rw [witness_gram, witness_gram_inverse]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessGramInv, witnessB, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_B_rightInverse : IsRightInverse witnessA witnessB := by
  unfold IsRightInverse
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessB, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_X_rightInverse : IsRightInverse witnessA witnessX := by
  unfold IsRightInverse
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessX, Matrix.mul_apply, Fin.sum_univ_succ]

lemma witness_fullRowRank : FullRowRank witnessA := by
  apply le_antisymm (Matrix.rank_le_height witnessA)
  have h := Matrix.rank_mul_le_left witnessA witnessX
  rw [show witnessA * witnessX = 1 from witness_X_rightInverse, Matrix.rank_one] at h
  simpa using h

lemma witness_B_ne_X : witnessB ≠ witnessX := by
  intro h
  have h0 := congrArg (fun M : Mat 3 2 => M 0 0) h
  norm_num [witnessB, witnessX] at h0

lemma witness_B_gram : witnessB.conjTranspose * witnessB = witnessGramInv := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessB, witnessGramInv, Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat]

lemma witness_X_gram : witnessX.conjTranspose * witnessX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessX, Matrix.mul_apply, Fin.sum_univ_succ]

end NLA.IE23
