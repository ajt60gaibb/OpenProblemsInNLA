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
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.MF24

open scoped BigOperators
noncomputable section

private lemma even_sign (n : ℕ) : (-1 : ℂ) ^ (n + n) = 1 := by
  rw [show n + n = 2 * n by omega, pow_mul]
  norm_num

private lemma odd_sign (n : ℕ) : (-1 : ℂ) ^ (n + 1 + n) = -1 := by
  rw [show n + 1 + n = (n + n) + 1 by omega, pow_succ, even_sign]
  norm_num

/-- Two Laplace expansions give the last-border identity without any inverse
or nonzero-minor hypothesis. This also covers the empty second minor at n=0. -/
theorem last_border_det (n : ℕ) (A : Square (n + 2))
    (hrow : ∀ i : Fin n,
      A (Fin.last (n + 1)) i.castSucc.castSucc = 0)
    (hcol : ∀ i : Fin n,
      A i.castSucc.castSucc (Fin.last (n + 1)) = 0) :
    A.det =
      A (Fin.last (n + 1)) (Fin.last (n + 1)) *
        (A.submatrix Fin.castSucc Fin.castSucc).det -
      A (Fin.last (n + 1)) (Fin.last n).castSucc *
        A (Fin.last n).castSucc (Fin.last (n + 1)) *
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
  let B : Square (n + 1) :=
    A.submatrix Fin.castSucc (Fin.last n).castSucc.succAbove
  have hBcol (i : Fin n) : B i.castSucc (Fin.last n) = 0 := by
    simpa [B] using hcol i
  have hBlast : B (Fin.last n) (Fin.last n) =
      A (Fin.last n).castSucc (Fin.last (n + 1)) := by
    simp [B]
  have hBcorner : B.submatrix Fin.castSucc Fin.castSucc =
      A.submatrix (fun i : Fin n => i.castSucc.castSucc)
        (fun i : Fin n => i.castSucc.castSucc) := by
    ext i j
    simp [B]
  have hBdet : B.det =
      A (Fin.last n).castSucc (Fin.last (n + 1)) *
        (A.submatrix (fun i : Fin n => i.castSucc.castSucc)
          (fun i : Fin n => i.castSucc.castSucc)).det := by
    rw [Matrix.det_succ_column B (Fin.last n), Fin.sum_univ_castSucc]
    simp only [hBcol, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
      Fin.val_last, even_sign, one_mul, Fin.succAbove_last, hBlast, hBcorner]
  rw [Matrix.det_succ_row A (Fin.last (n + 1)),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hrow, mul_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Fin.val_last, Fin.val_castSucc, even_sign, odd_sign,
    one_mul, neg_one_mul, Fin.succAbove_last]
  change -A (Fin.last (n + 1)) (Fin.last n).castSucc * B.det + _ = _
  rw [hBdet]
  ring

end
end NLA.MF24
