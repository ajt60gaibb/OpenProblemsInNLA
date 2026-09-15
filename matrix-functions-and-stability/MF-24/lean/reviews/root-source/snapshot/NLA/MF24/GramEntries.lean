/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Definitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.MF24

open scoped BigOperators
noncomputable section

/-- The actual Gram pencil inside `leadingGramDet`, with no positivity or
reality condition on its two complex parameters. -/
def gramPencil (word : List ℝ) (z η : ℂ) (n : ℕ) : Square n :=
  gram (scalarShift (wordShift word n) z) + η • (1 : Square n)

private lemma shiftedWord_diag (word : List ℝ) (z : ℂ) {n : ℕ} (i : Fin n) :
    scalarShift (wordShift word n) z i i = -z := by
  have hi : ¬i.val + 1 = i.val := by omega
  simp [scalarShift, wordShift, Matrix.one_apply, hi]

private lemma shiftedWord_zero (word : List ℝ) (z : ℂ) {n : ℕ} (i j : Fin n)
    (hij : i ≠ j) (hstep : i.val + 1 ≠ j.val) :
    scalarShift (wordShift word n) z i j = 0 := by
  simp [scalarShift, wordShift, Matrix.one_apply, hij, hstep]

private lemma shiftedWord_lower (word : List ℝ) (z : ℂ) {n : ℕ} (i j : Fin n)
    (hij : j.val < i.val) : scalarShift (wordShift word n) z i j = 0 := by
  apply shiftedWord_zero
  · exact (Fin.ne_iff_vne i j).mpr (by omega)
  · omega

private lemma shiftedWord_corner (word : List ℝ) (z : ℂ) (n : ℕ)
    (i j : Fin n) :
    scalarShift (wordShift word (n + 1)) z i.castSucc j.castSucc =
      scalarShift (wordShift word n) z i j := by
  simp [scalarShift, wordShift, Matrix.one_apply]

private lemma shiftedWord_last_lower (word : List ℝ) (z : ℂ) (n : ℕ)
    (j : Fin n) :
    scalarShift (wordShift word (n + 1)) z (Fin.last n) j.castSucc = 0 := by
  apply shiftedWord_lower
  exact j.isLt

private lemma shiftedWord_far_upper (word : List ℝ) (z : ℂ) (n : ℕ)
    (i : Fin n) : scalarShift (wordShift word (n + 2)) z
      i.castSucc.castSucc (Fin.last (n + 1)) = 0 := by
  apply shiftedWord_zero
  · simp
  · simp only [Fin.val_castSucc, Fin.val_last]
    omega

private lemma shiftedWord_last_edge (word : List ℝ) (z : ℂ) (n : ℕ) :
    scalarShift (wordShift word (n + 2)) z
      (Fin.last n).castSucc (Fin.last (n + 1)) = (word.getD n 0 : ℂ) := by
  simp [scalarShift, wordShift, Matrix.one_apply]

private lemma shiftedWord_penultimate_lower (word : List ℝ) (z : ℂ) (n : ℕ)
    (i : Fin n) : scalarShift (wordShift word (n + 2)) z
      (Fin.last n).castSucc i.castSucc.castSucc = 0 := by
  apply shiftedWord_lower
  exact i.isLt

lemma gramPencil_apply (word : List ℝ) (z η : ℂ) (n : ℕ) (i j : Fin n) :
    gramPencil word z η n i j =
      (∑ k : Fin n, star (scalarShift (wordShift word n) z k i) *
        scalarShift (wordShift word n) z k j) + if i = j then η else 0 := by
  by_cases hij : i = j <;>
    simp [gramPencil, gram, Matrix.mul_apply, Matrix.one_apply, hij]

/-- Leading principal corners of the actual Gram pencils agree. The new
row of the shifted upper bidiagonal matrix is zero in all earlier columns. -/
theorem gramPencil_corner (word : List ℝ) (z η : ℂ) (n : ℕ) :
    (gramPencil word z η (n + 1)).submatrix Fin.castSucc Fin.castSucc =
      gramPencil word z η n := by
  ext i j
  change gramPencil word z η (n + 1) i.castSucc j.castSucc =
    gramPencil word z η n i j
  simp only [gramPencil_apply, Fin.sum_univ_castSucc, shiftedWord_corner,
    shiftedWord_last_lower, star_zero, zero_mul, add_zero, Fin.castSucc_inj]

theorem gramPencil_last_last (word : List ℝ) (z η : ℂ) (n : ℕ) :
    gramPencil word z η (n + 2) (Fin.last (n + 1)) (Fin.last (n + 1)) =
      shiftRadiusSq z + η + (word.getD n 0 : ℂ) ^ 2 := by
  rw [gramPencil_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shiftedWord_far_upper, shiftedWord_last_edge, shiftedWord_diag,
    shiftRadiusSq, Complex.normSq_eq_conj_mul_self, pow_two]
  ring

theorem gramPencil_last_previous (word : List ℝ) (z η : ℂ) (n : ℕ) :
    gramPencil word z η (n + 2) (Fin.last (n + 1)) (Fin.last n).castSucc =
      -z * (word.getD n 0 : ℂ) := by
  rw [gramPencil_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shiftedWord_far_upper, shiftedWord_last_edge, shiftedWord_diag,
    shiftedWord_last_lower, mul_comm]

theorem gramPencil_previous_last (word : List ℝ) (z η : ℂ) (n : ℕ) :
    gramPencil word z η (n + 2) (Fin.last n).castSucc (Fin.last (n + 1)) =
      -star z * (word.getD n 0 : ℂ) := by
  rw [gramPencil_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shiftedWord_far_upper, shiftedWord_last_edge, shiftedWord_diag,
    shiftedWord_last_lower]

theorem gramPencil_last_earlier (word : List ℝ) (z η : ℂ) (n : ℕ) (i : Fin n) :
    gramPencil word z η (n + 2) (Fin.last (n + 1)) i.castSucc.castSucc = 0 := by
  rw [gramPencil_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shiftedWord_far_upper, shiftedWord_penultimate_lower, shiftedWord_last_lower]

theorem gramPencil_earlier_last (word : List ℝ) (z η : ℂ) (n : ℕ) (i : Fin n) :
    gramPencil word z η (n + 2) i.castSucc.castSucc (Fin.last (n + 1)) = 0 := by
  rw [gramPencil_apply, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp [shiftedWord_far_upper, shiftedWord_penultimate_lower, shiftedWord_last_lower]

theorem gramPencil_zero_det (word : List ℝ) (z η : ℂ) :
    (gramPencil word z η 0).det = 1 := Matrix.det_fin_zero

theorem gramPencil_one_det (word : List ℝ) (z η : ℂ) :
    (gramPencil word z η 1).det = shiftRadiusSq z + η := by
  rw [Matrix.det_fin_one, gramPencil_apply]
  simp [Fin.sum_univ_one, shiftedWord_diag, shiftRadiusSq, Complex.normSq_eq_conj_mul_self]

end
end NLA.MF24
