/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

Source: Matthew J. Colbrook, University of Cambridge, NR-04 manuscript,
Section 5. A literal three-column ordinary factorization proves rank at most
three; a nonzero leading minor proves rank at least three. The latter actually
consumes the kernel-mode LeanCert positivity certificate from Numerical.
Ordinary matrix rank is not substituted for nonnegative rank.
-/
import NLA.NR04.Numerical
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.NR04

private def ordinaryLeft : Matrix (Fin 9) (Fin 3) ℝ := fun i r =>
  if r = 0 then (i.val : ℝ) ^ 2 else if r = 1 then (i.val : ℝ) else 1

private def ordinaryRight : Matrix (Fin 3) (Fin 9) ℝ := fun r j =>
  if r = 0 then 1 else if r = 1 then -2 * (j.val : ℝ) else (j.val : ℝ) ^ 2

private lemma ordinary_product : ordinaryLeft * ordinaryRight = distanceNine := by
  ext i j
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  norm_num [Matrix.mul_apply, Fin.sum_univ_three, ordinaryLeft, ordinaryRight,
    distanceNine, h20, h21] <;> ring

/-- C06: the upper and lower bounds refer to Mathlib's actual matrix rank. -/
theorem distance_rank_certificate :
    (distanceNine.submatrix firstThree firstThree).det = 8 ∧
      distanceNine.rank = 3 := by
  have hdet : (distanceNine.submatrix firstThree firstThree).det = 8 := by
    norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, firstThree, distanceNine]
  refine ⟨hdet, le_antisymm ?_ ?_⟩
  · rw [← ordinary_product]
    exact (Matrix.rank_mul_le_left ordinaryLeft ordinaryRight).trans
      (Matrix.rank_le_width ordinaryLeft)
  · have hnonzero : (distanceNine.submatrix firstThree firstThree).det ≠ 0 := by
      rw [hdet]
      exact ne_of_gt minor_eight_positive
    have hminor : (distanceNine.submatrix firstThree firstThree).rank = 3 := by
      simpa using Matrix.rank_of_det_ne_zero hnonzero
    calc
      3 = (distanceNine.submatrix firstThree firstThree).rank := hminor.symm
      _ ≤ distanceNine.rank :=
        Matrix.rank_submatrix_le distanceNine firstThree firstThree

#print axioms distance_rank_certificate
#assert_trust kernel distance_rank_certificate

end NLA.NR04
