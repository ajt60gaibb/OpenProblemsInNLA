/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.GramContinuant

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

open scoped BigOperators
noncomputable section

/-- Prefix extension puts the new edge matrix on the left, exactly matching
the reversal in the frozen transfer-product definition. -/
private theorem prefix_product_step (word : List ℝ) (u ρ : ℂ) (k : ℕ)
    (hk : k < word.length) :
    transferProduct u ρ (word.take (k + 1)) =
      transferMatrix u ρ ((word.getD k 0 : ℂ) ^ 2) *
        transferProduct u ρ (word.take k) := by
  rw [List.take_succ_eq_append_getElem hk, List.getD_eq_getElem word 0 hk]
  simp [transferProduct, List.reverse_append]

/-- Both coordinates track actual Gram determinants throughout the entire
prefix, so the scalar recurrence is connected to the ordered matrix product. -/
private theorem prefix_transfer (word : List ℝ) (z η : ℂ) (k : ℕ) :
    k ≤ word.length →
      Matrix.mulVec (transferProduct (shiftRadiusSq z + η) (shiftRadiusSq z)
        (word.take k)) (transferInitial (shiftRadiusSq z + η)) =
        ![leadingGramDet word z η (k + 1), leadingGramDet word z η k] := by
  induction k with
  | zero =>
      intro _
      simp [transferProduct, transferInitial,
        (gram_continuant word z η).1, (gram_continuant word z η).2.1]
  | succ k ih =>
      intro hk
      have hlt : k < word.length := by omega
      rw [prefix_product_step word _ _ k hlt, ← Matrix.mulVec_mulVec,
        ih (Nat.le_of_lt hlt)]
      have hrec := leadingGramDet_succ_succ word z η k
      ext i
      fin_cases i
      · simpa [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
          sub_eq_add_neg, mul_assoc] using hrec.symm
      · simp [transferMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Correctly ordered transfer product for the full actual determinant. -/
theorem gram_transfer (word : List ℝ) (z η : ℂ) :
    leadingGramDet word z η (word.length + 1) =
      transferValue (shiftRadiusSq z + η) (shiftRadiusSq z) word := by
  have h := prefix_transfer word z η word.length le_rfl
  have hzero := congrArg (fun v : Fin 2 → ℂ => v 0) h
  simpa [transferValue] using hzero.symm

#assert_trust kernel gram_transfer
#print axioms gram_transfer

end
end NLA.MF24
