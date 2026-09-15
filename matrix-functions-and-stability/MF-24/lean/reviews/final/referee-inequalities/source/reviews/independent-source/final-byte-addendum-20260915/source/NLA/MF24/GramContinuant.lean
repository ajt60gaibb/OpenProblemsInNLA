/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Continuant
import NLA.MF24.GramEntries
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

noncomputable section

/-- The recurrence actually holds at every order, including padded zero edges.
The public statement below restricts to the source word's ordinary range. -/
theorem leadingGramDet_succ_succ (word : List ℝ) (z η : ℂ) (n : ℕ) :
    leadingGramDet word z η (n + 2) =
      (shiftRadiusSq z + η + (word.getD n 0 : ℂ) ^ 2) *
        leadingGramDet word z η (n + 1) -
      shiftRadiusSq z * (word.getD n 0 : ℂ) ^ 2 * leadingGramDet word z η n := by
  have hcorner :
      (gramPencil word z η (n + 2)).submatrix
        (fun i : Fin n => i.castSucc.castSucc)
        (fun i : Fin n => i.castSucc.castSucc) = gramPencil word z η n := by
    calc
      _ = Matrix.submatrix
          ((gramPencil word z η (n + 2)).submatrix Fin.castSucc Fin.castSucc)
          Fin.castSucc Fin.castSucc := rfl
      _ = gramPencil word z η n := by
        rw [gramPencil_corner, gramPencil_corner]
  have h := last_border_det n (gramPencil word z η (n + 2))
    (gramPencil_last_earlier word z η n) (gramPencil_earlier_last word z η n)
  rw [gramPencil_last_last, gramPencil_last_previous, gramPencil_previous_last,
    gramPencil_corner, hcorner] at h
  change (gramPencil word z η (n + 2)).det =
    (shiftRadiusSq z + η + (word.getD n 0 : ℂ) ^ 2) *
      (gramPencil word z η (n + 1)).det -
    shiftRadiusSq z * (word.getD n 0 : ℂ) ^ 2 * (gramPencil word z η n).det
  rw [h]
  simp only [shiftRadiusSq, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

/-- Generic continuant recurrence for the actual leading Gram determinants.
All complex shifts and all complex η are quantified. Positivity of weights
is unnecessary for this algebraic identity and is not assumed. -/
theorem gram_continuant (word : List ℝ) (z η : ℂ) :
    leadingGramDet word z η 0 = 1 ∧
    leadingGramDet word z η 1 = shiftRadiusSq z + η ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ word.length →
      leadingGramDet word z η (j + 1) =
        (shiftRadiusSq z + η + (word.getD (j - 1) 0 : ℂ) ^ 2) *
          leadingGramDet word z η j -
        shiftRadiusSq z * (word.getD (j - 1) 0 : ℂ) ^ 2 *
          leadingGramDet word z η (j - 1) := by
  refine ⟨gramPencil_zero_det word z η, gramPencil_one_det word z η, ?_⟩
  intro j hj _
  cases j with
  | zero => omega
  | succ n =>
      simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
        leadingGramDet_succ_succ word z η n

#assert_trust kernel gram_continuant
#print axioms gram_continuant

end
end NLA.MF24
