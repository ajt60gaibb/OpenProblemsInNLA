/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook.
-/
import NLA.MF16.Algebra
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace NLA.MF16
open LeanCert.Core LeanCert.Engine

/-- Symmetry and the actual determinant recover the entry not checked by the system. -/
theorem word_eq_of_two_entries (v : Fin 3 → ℝ)
    (hdet : (symmetricMatrix v).det = 3)
    (h00 : (evalWord witnessWord (symmetricMatrix v) realB) 0 0 = realP 0 0)
    (h01 : (evalWord witnessWord (symmetricMatrix v) realB) 0 1 = realP 0 1) :
    evalWord witnessWord (symmetricMatrix v) realB = realP := by
  have h10 : (evalWord witnessWord (symmetricMatrix v) realB) 1 0 =
      (evalWord witnessWord (symmetricMatrix v) realB) 0 1 :=
    congrArg (fun A : RealMatrix => A 0 1) (witness_word_transpose v)
  have hd := witness_word_det v hdet
  rw [Matrix.det_fin_two,h00,h10,h01] at hd
  norm_num [realP] at hd
  have h11 : (evalWord witnessWord (symmetricMatrix v) realB) 1 1 = realP 1 1 := by
    norm_num [realP]
    linarith [hd]
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10.trans h01
  · exact h11

theorem box_first_coordinate_gt_three (v : Fin 3 → ℝ) (hv : FinBoxMem v rootBox) :
    3 < v 0 := by
  have hlo : ((rootBox 0).lo : ℝ) ≤ v 0 := (hv 0).1
  norm_num [rootBox] at hlo
  linarith

/-- The boxed real solution becomes a distinct complex Hermitian PD solution. -/
theorem matrix_recovery_from_equations (v : Fin 3 → ℝ) (hv : FinBoxMem v rootBox)
    (hdet : (symmetricMatrix v).det = 3)
    (h00 : (evalWord witnessWord (symmetricMatrix v) realB) 0 0 = realP 0 0)
    (h01 : (evalWord witnessWord (symmetricMatrix v) realB) 0 1 = realP 0 1) :
    3 < v 0 ∧ (complexify (symmetricMatrix v)).PosDef ∧
    evalWord witnessWord (complexify (symmetricMatrix v)) witnessB = witnessP ∧
    complexify (symmetricMatrix v) ≠ witnessX0 := by
  have hx := box_first_coordinate_gt_three v hv
  have hd : v 0 * v 2 - v 1 * v 1 = 3 := by
    simpa [symmetricMatrix,Matrix.det_fin_two] using hdet
  have hp : (complexify (symmetricMatrix v)).PosDef :=
    complexify_two_by_two_posDef (v 0) (v 1) (v 2) (by linarith) (by rw [hd]; norm_num)
  have heq := word_eq_of_two_entries v hdet h00 h01
  refine ⟨hx,hp,?_,?_⟩
  · simpa only [complexify_witness_eval,witnessB,witnessP] using congrArg complexify heq
  · intro h
    have hentry := congrArg (fun A : ComplexMatrix => (A 0 0).re) h
    norm_num [complexify,symmetricMatrix,witnessX0,realX0] at hentry
    linarith

end NLA.MF16
