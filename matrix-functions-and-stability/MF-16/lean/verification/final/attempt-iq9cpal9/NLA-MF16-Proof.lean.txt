/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook. The helper author and main
implementation author are implementation coauthors, not final referees.
-/
import NLA.MF16.Numerical
import NLA.MF16.CayleyHamilton
import NLA.MF16.Polynomial
import NLA.MF16.Recovery

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped ComplexOrder
noncomputable section
namespace NLA.MF16
open LeanCert.Core LeanCert.Engine

theorem reducedWord_eq (v : Fin 3 → ℝ) (hdet : (symmetricMatrix v).det = 3) :
    reducedWord v = evalWord witnessWord (symmetricMatrix v) realB := by
  unfold reducedWord
  rw [witness_eval,twelfth_power_reduction_proved v hdet]

/-- The det-three premise needed by Cayley–Hamilton is proved by system component zero. -/
theorem polynomial_word_equivalence_proved (v : Fin 3 → ℝ) :
    SystemZero polynomialSystem v ↔
      (symmetricMatrix v).det = 3 ∧
      (evalWord witnessWord (symmetricMatrix v) realB) 0 0 = realP 0 0 ∧
      (evalWord witnessWord (symmetricMatrix v) realB) 0 1 = realP 0 1 := by
  rw [polynomial_reduced_equivalence]
  constructor <;> rintro ⟨hd,h00,h01⟩
  · exact ⟨hd,by simpa only [reducedWord_eq v hd] using h00,
      by simpa only [reducedWord_eq v hd] using h01⟩
  · exact ⟨hd,by simpa only [reducedWord_eq v hd] using h00,
      by simpa only [reducedWord_eq v hd] using h01⟩

theorem root_to_matrix_proved (v : Fin 3 → ℝ) (hv : FinBoxMem v rootBox)
    (hz : SystemZero polynomialSystem v) :
    3 < v 0 ∧ (complexify (symmetricMatrix v)).PosDef ∧
    evalWord witnessWord (complexify (symmetricMatrix v)) witnessB = witnessP ∧
    complexify (symmetricMatrix v) ≠ witnessX0 := by
  rcases (polynomial_word_equivalence_proved v).mp hz with ⟨hd,h00,h01⟩
  exact matrix_recovery_from_equations v hv hd h00 h01

theorem counterexample_proved :
    SymmetricWord witnessWord ∧ witnessB.PosDef ∧ witnessP.PosDef ∧
    witnessX0.PosDef ∧ evalWord witnessWord witnessX0 witnessB = witnessP ∧
    ∃ X : ComplexMatrix, X.PosDef ∧
      evalWord witnessWord X witnessB = witnessP ∧ X ≠ witnessX0 := by
  obtain ⟨v,⟨hv,hz⟩,_⟩ := certified_root_proved
  obtain ⟨_,hp,heq,hne⟩ := root_to_matrix_proved v hv hz
  exact ⟨word_semantics_proved.1,source_data_proved.1,source_data_proved.2.1,
    source_data_proved.2.2.1,source_data_proved.2.2.2.1,
    complexify (symmetricMatrix v),hp,heq,hne⟩

/-- A second actual complex PD solution contradicts the full original universal uniqueness. -/
theorem not_wordUniquenessConjecture_proved : ¬ WordUniquenessConjecture := by
  intro h
  rcases counterexample_proved with ⟨hw,hb,hp,hx0,heq0,X,hx,heq,hne⟩
  obtain ⟨Y,_,hu⟩ := h witnessWord hw witnessB witnessP hb hp
  exact hne ((hu X ⟨hx,heq⟩).trans (hu witnessX0 ⟨hx0,heq0⟩).symm)

#assert_trust kernel reducedWord_eq
#assert_trust kernel polynomial_word_equivalence_proved
#assert_trust kernel root_to_matrix_proved
#assert_trust kernel counterexample_proved
#assert_trust kernel not_wordUniquenessConjecture_proved
#print axioms reducedWord_eq
#print axioms polynomial_word_equivalence_proved
#print axioms root_to_matrix_proved
#print axioms counterexample_proved
#print axioms not_wordUniquenessConjecture_proved

end NLA.MF16
