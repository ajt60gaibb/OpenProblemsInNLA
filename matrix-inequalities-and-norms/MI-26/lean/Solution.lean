/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Complete formalization of Matthew J. Colbrook's counterexample to MI-26.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI26.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI26

/-- Mathlib's concavity predicate is exactly the scalar definition in the problem. -/
theorem admissibleFunction_iff (f : ℝ → ℝ) :
    AdmissibleFunction f ↔
      (0 ≤ f 0 ∧ ∀ x y θ : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ θ → θ ≤ 1 →
        θ * f x + (1 - θ) * f y ≤ f (θ * x + (1 - θ) * y)) := by
  exact admissibleFunction_iff_proved f

/-- Genuine CFC agrees with the complete spectral definition for every real
function and every Hermitian complex matrix, without a continuity premise. -/
theorem functionalCalculus_eq_spectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    functionalCalculus f A =
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  exact functionalCalculus_eq_spectral_proved A hA f

/-- Values outside the original nonnegative half-line have no effect on PSD inputs. -/
theorem functionalCalculus_congr_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (f g : ℝ → ℝ) (hfg : Set.EqOn f g (Set.Ici 0)) :
    functionalCalculus f A = functionalCalculus g A := by
  exact functionalCalculus_congr_nonneg_proved A hA f g hfg

/-- The numerical polynomial calculation is linked to genuine CFC for every
Hermitian matrix, including both projections and their sum. -/
theorem quadratic_cfc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    functionalCalculus witnessFunction A = A - A ^ 2 := by
  exact quadratic_cfc_proved A hA

/-- All admissibility and exact matrix/scalar obligations of the source witness.
The final strictly positive real scalar has an explicit kernel LeanCert
certificate that is consumed by the subsequent unitary exclusion. -/
theorem witness_data :
    AdmissibleFunction witnessFunction ∧
    witnessFunction 0 = 0 ∧ witnessFunction 2 = -2 ∧
    witnessP.PosSemidef ∧ witnessQ.PosSemidef ∧
    witnessP ^ 2 = witnessP ∧ witnessQ ^ 2 = witnessQ ∧
    functionalCalculus witnessFunction witnessP = 0 ∧
    functionalCalculus witnessFunction witnessQ = 0 ∧
    functionalCalculus witnessFunction (witnessP + witnessQ) = witnessImage ∧
    witnessVector ≠ 0 ∧
    star witnessVector ⬝ᵥ (witnessImage *ᵥ witnessVector) = (6 / 5 : ℂ) ∧
    (0 : ℝ) < 6 / 5 := by
  exact witness_data_proved

/-- No pair of complex unitaries satisfies the original inequality at the witness. -/
theorem counterexample (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ¬ (functionalCalculus witnessFunction (witnessP + witnessQ) ≤
      unitaryConjugate U (functionalCalculus witnessFunction witnessP) +
        unitaryConjugate V (functionalCalculus witnessFunction witnessQ)) := by
  exact counterexample_proved U V

/-- Negation of the complete canonical target, with all original quantifiers. -/
theorem not_subadditivityConjecture : ¬ SubadditivityConjecture := by
  exact not_subadditivityConjecture_proved

#assert_trust kernel admissibleFunction_iff
#assert_trust kernel functionalCalculus_eq_spectral
#assert_trust kernel functionalCalculus_congr_nonneg
#assert_trust kernel quadratic_cfc
#assert_trust kernel witness_data
#assert_trust kernel counterexample
#assert_trust kernel not_subadditivityConjecture

#print axioms admissibleFunction_iff
#print axioms functionalCalculus_eq_spectral
#print axioms functionalCalculus_congr_nonneg
#print axioms quadratic_cfc
#print axioms witness_data
#print axioms counterexample
#print axioms not_subadditivityConjecture

end NLA.MI26
