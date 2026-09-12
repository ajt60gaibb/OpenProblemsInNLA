/-
Frozen statement-only interface for Matthew J. Colbrook's MI-26 counterexample.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
The intentional placeholders in this challenge are never implementation proofs.
-/
import NLA.MI26.Definitions

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
open Matrix
noncomputable section

namespace NLA.MI26

/-- Mathlib's concavity predicate is exactly the scalar definition in the problem. -/
theorem admissibleFunction_iff (f : ℝ → ℝ) :
    AdmissibleFunction f ↔
      (0 ≤ f 0 ∧ ∀ x y θ : ℝ, 0 ≤ x → 0 ≤ y → 0 ≤ θ → θ ≤ 1 →
        θ * f x + (1 - θ) * f y ≤ f (θ * x + (1 - θ) * y)) := by
  sorry

/-- Genuine CFC agrees with the complete spectral definition for every real
function and every Hermitian complex matrix, without a continuity premise. -/
theorem functionalCalculus_eq_spectral {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    functionalCalculus f A =
      (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *
        Matrix.diagonal (fun i => (f (hA.eigenvalues i) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ).conjTranspose := by
  sorry

/-- Values outside the original nonnegative half-line have no effect on PSD inputs. -/
theorem functionalCalculus_congr_nonneg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosSemidef)
    (f g : ℝ → ℝ) (hfg : Set.EqOn f g (Set.Ici 0)) :
    functionalCalculus f A = functionalCalculus g A := by
  sorry

/-- The numerical polynomial calculation is linked to genuine CFC for every
Hermitian matrix, including both projections and their sum. -/
theorem quadratic_cfc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsHermitian) :
    functionalCalculus witnessFunction A = A - A ^ 2 := by
  sorry

/-- All admissibility and exact matrix/scalar obligations of the source witness.
The final strictly positive real scalar is to have an explicit kernel LeanCert
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
  sorry

/-- No pair of complex unitaries satisfies the original inequality at the witness. -/
theorem counterexample (U V : Matrix.unitaryGroup (Fin 2) ℂ) :
    ¬ (functionalCalculus witnessFunction (witnessP + witnessQ) ≤
      unitaryConjugate U (functionalCalculus witnessFunction witnessP) +
        unitaryConjugate V (functionalCalculus witnessFunction witnessQ)) := by
  sorry

/-- Negation of the complete canonical target, with all original quantifiers. -/
theorem not_subadditivityConjecture : ¬ SubadditivityConjecture := by
  sorry

end NLA.MI26
