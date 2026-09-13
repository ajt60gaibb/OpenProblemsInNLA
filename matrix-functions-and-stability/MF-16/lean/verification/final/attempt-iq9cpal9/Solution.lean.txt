/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical counterexample: Matthew J. Colbrook. Complete implementations of
the nine frozen Challenge contracts; Challenge is not imported.
-/
import NLA.MF16.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped ComplexOrder
namespace NLA.MF16
open LeanCert.Core LeanCert.Engine

theorem word_semantics :
    SymmetricWord witnessWord ∧ witnessWord.length = 16 ∧
    witnessWord.count Letter.X = 14 ∧ witnessWord.count Letter.B = 2 ∧
    (∀ X B : ComplexMatrix,
      evalWord witnessWord X B = X * B * X^12 * B * X) ∧
    (∀ X B : RealMatrix,
      evalWord witnessWord X B = X * B * X^12 * B * X) :=
  word_semantics_proved

theorem source_data :
    witnessB.PosDef ∧ witnessP.PosDef ∧ witnessX0.PosDef ∧
    evalWord witnessWord witnessX0 witnessB = witnessP ∧
    realB.det = 1 ∧ realX0.det = 3 ∧ realP.det = 3^14 :=
  source_data_proved

theorem twelfth_power_reduction (v : Fin 3 → ℝ)
    (hdet : (symmetricMatrix v).det = 3) :
    (symmetricMatrix v)^12 =
      linearCoefficient (Matrix.trace (symmetricMatrix v)) • symmetricMatrix v -
      identityCoefficient (Matrix.trace (symmetricMatrix v)) • (1 : RealMatrix) :=
  twelfth_power_reduction_proved v hdet

theorem polynomial_word_equivalence (v : Fin 3 → ℝ) :
    SystemZero polynomialSystem v ↔
      (symmetricMatrix v).det = 3 ∧
      (evalWord witnessWord (symmetricMatrix v) realB) 0 0 = realP 0 0 ∧
      (evalWord witnessWord (symmetricMatrix v) realB) 0 1 = realP 0 1 :=
  polynomial_word_equivalence_proved v

theorem krawczyk_certificate :
    krawczykCheck polynomialSystem rootBox rootCertificate {} = true ∧
    rootCertificate.preconditioner.det =
      (790668616748253/62500000000000000000000000000 : ℚ) ∧
    boxRadius rootBox rootCenter = rootRadius ∧
    contractionBound < 27/1000 :=
  ⟨actual_krawczyk_checked,preconditioner_det_exact,box_radius_exact,contraction_bound_small⟩

theorem certified_root :
    ∃! v : Fin 3 → ℝ, FinBoxMem v rootBox ∧ SystemZero polynomialSystem v :=
  certified_root_proved

theorem root_to_matrix (v : Fin 3 → ℝ) (hv : FinBoxMem v rootBox)
    (hz : SystemZero polynomialSystem v) :
    3 < v 0 ∧ (complexify (symmetricMatrix v)).PosDef ∧
    evalWord witnessWord (complexify (symmetricMatrix v)) witnessB = witnessP ∧
    complexify (symmetricMatrix v) ≠ witnessX0 :=
  root_to_matrix_proved v hv hz

theorem counterexample :
    SymmetricWord witnessWord ∧ witnessB.PosDef ∧ witnessP.PosDef ∧
    witnessX0.PosDef ∧ evalWord witnessWord witnessX0 witnessB = witnessP ∧
    ∃ X : ComplexMatrix, X.PosDef ∧
      evalWord witnessWord X witnessB = witnessP ∧ X ≠ witnessX0 :=
  counterexample_proved

theorem not_wordUniquenessConjecture : ¬ WordUniquenessConjecture :=
  not_wordUniquenessConjecture_proved

#assert_trust kernel word_semantics
#assert_trust kernel source_data
#assert_trust kernel twelfth_power_reduction
#assert_trust kernel polynomial_word_equivalence
#assert_trust kernel krawczyk_certificate
#assert_trust kernel certified_root
#assert_trust kernel root_to_matrix
#assert_trust kernel counterexample
#assert_trust kernel not_wordUniquenessConjecture
#print axioms word_semantics
#print axioms source_data
#print axioms twelfth_power_reduction
#print axioms polynomial_word_equivalence
#print axioms krawczyk_certificate
#print axioms certified_root
#print axioms root_to_matrix
#print axioms counterexample
#print axioms not_wordUniquenessConjecture

end NLA.MF16
