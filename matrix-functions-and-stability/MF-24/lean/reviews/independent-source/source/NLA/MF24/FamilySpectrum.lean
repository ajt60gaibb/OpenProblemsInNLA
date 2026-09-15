/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Transfer
import NLA.MF24.FamilyTransfer
import NLA.MF24.SpectralBridge
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

lemma charpoly_eq_of_all_shifted_determinants {N : ℕ} (A B : Square N)
    (h : ∀ η : ℂ, (A + η • (1 : Square N)).det = (B + η • (1 : Square N)).det) :
    A.charpoly = B.charpoly := by
  apply Polynomial.funext
  intro λ
  rw [Matrix.eval_charpoly, Matrix.eval_charpoly]
  have hs : Matrix.scalar (Fin N) λ = λ • (1 : Square N) := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply, hij]
  have hneg (C : Square N) : Matrix.scalar (Fin N) λ - C = -(C + (-λ) • (1 : Square N)) := by
    rw [hs]
    module
  rw [hneg A, hneg B, Matrix.det_neg, Matrix.det_neg, h (-λ)]

lemma family_gram_determinant (m : ℕ) (hm : 2 ≤ m) (t : ℝ) (z η : ℂ) :
    (gram (scalarShift (matrixX m t) z) + η • (1 : Square (dimension m))).det =
    (gram (scalarShift (matrixY m t) z) + η • (1 : Square (dimension m))).det := by
  have hd := family_dimensions m hm t
  have hXlen : (sourceWordX m t).length + 1 = dimension m := by omega
  have hYlen : (sourceWordY m t).length + 1 = dimension m := by omega
  have hX := gram_transfer (sourceWordX m t) z η
  have hY := gram_transfer (sourceWordY m t) z η
  rw [hXlen] at hX
  rw [hYlen] at hY
  change (gram (scalarShift (matrixX m t) z) + η • (1 : Square (dimension m))).det = _ at hX
  change (gram (scalarShift (matrixY m t) z) + η • (1 : Square (dimension m))).det = _ at hY
  exact hX.trans ((family_transfer_value_eq m t (shiftRadiusSq z + η) (shiftRadiusSq z)).trans hY.symm)

theorem family_gram_charpoly (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) (z : ℂ) :
    (gram (scalarShift (matrixX m t) z)).charpoly =
      (gram (scalarShift (matrixY m t) z)).charpoly :=
  charpoly_eq_of_all_shifted_determinants _ _ (family_gram_determinant m hm t z)

theorem family_super_identical (m : ℕ) (hm : 2 ≤ m)
    (t : ℝ) (ht : 1 < t) :
    SuperIdentical (matrixX m t) (matrixY m t) := by
  intro z j
  exact gram_singular_bridge (dimension m) (scalarShift (matrixX m t) z)
    (scalarShift (matrixY m t) z) (family_gram_charpoly m hm t ht z) j

#assert_trust kernel family_gram_charpoly
#assert_trust kernel family_super_identical
#print axioms family_gram_charpoly
#print axioms family_super_identical

end NLA.MF24
