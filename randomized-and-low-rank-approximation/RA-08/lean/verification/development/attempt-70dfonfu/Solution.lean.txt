/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact exports of the independently reviewed RA-08 Challenge contracts.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA08.Proof

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
open Matrix
noncomputable section
namespace NLA.RA08

/-- No vacuous restriction to an unavailable spectral representation: every
real PSD matrix admits complete ordered data, including repeated eigenvalues. -/
theorem orderedSpectral_exists {n : ℕ} (A : RealMatrix n) (hA : A.PosSemidef) :
    Nonempty (OrderedSpectralData A) := by
  exact orderedSpectral_exists_proved A hA

/-- The selected columns really are an orthonormal eigenbasis of the actual
matrix, and the full eigenvalue combination reconstructs it. -/
theorem orderedSpectral_semantics {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) :
    A.PosSemidef ∧ spectralCombination d d.eigenvalues = A ∧
      (∀ i j : Fin n,
        (fun r => (d.orthogonal : RealMatrix n) r i) ⬝ᵥ
          (fun r => (d.orthogonal : RealMatrix n) r j) = if i = j then 1 else 0) ∧
      (∀ i : Fin n,
        A *ᵥ (fun r => (d.orthogonal : RealMatrix n) r i) =
          d.eigenvalues i • (fun r => (d.orthogonal : RealMatrix n) r i)) := by
  exact orderedSpectral_semantics_proved d

/-- Genuine CFC agrees with every selected spectral decomposition, not only
Mathlib's preferred one. Values off the nonnegative half-line have no effect. -/
theorem functionalCalculus_spectral {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (f : ℝ → ℝ) :
    functionalCalculus f A = spectralCombination d (fun i => f (d.eigenvalues i)) ∧
      (∀ g : ℝ → ℝ, Set.EqOn f g (Set.Ici 0) →
        functionalCalculus f A = functionalCalculus g A) := by
  exact functionalCalculus_spectral_proved d f

/-- Exact Euclidean operator-norm tails for the original and function
truncations, with the same selected eigenvectors and zero-based index `k`. -/
theorem spectral_tail_norms {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (k : ℕ) (hk : k < n)
    (f : ℝ → ℝ) (hf : AdmissibleFunction f) :
    spectralNorm (A - truncation d k) = d.eigenvalues ⟨k, hk⟩ ∧
      spectralNorm (functionalCalculus f A - functionTruncation d f k) =
        f (d.eigenvalues ⟨k, hk⟩) := by
  exact spectral_tail_norms_proved d k hk f hf

/-- Genuine Euclidean Rayleigh bound, valid even when the matrix is not PSD. -/
theorem operator_rayleigh_bound {n : ℕ} (A : RealMatrix n) (x : Fin n → ℝ) :
    |x ⬝ᵥ (A *ᵥ x)| ≤ spectralNorm A * (x ⬝ᵥ x) := by
  exact operator_rayleigh_bound_proved A x

/-- Source admissibility, actual projection identities and PSD order.
No numerical spectral premise is assumed for the witness. -/
theorem witness_data :
    AdmissibleFunction witnessFunction ∧ witnessFunction 0 = 0 ∧
    0 < witnessT ∧ witnessB + witnessT < 1 ∧
    witnessU.transpose * witnessU = 1 ∧
    witnessF ^ 2 = witnessF ∧ witnessF.PosSemidef ∧
    (1 - witnessF).PosSemidef ∧
    witnessApproximation.PosSemidef ∧ witnessMatrix.PosDef ∧
    witnessApproximation ≤ witnessMatrix := by
  exact witness_data_proved

/-- Actual spectral containment of the fixed witness, derived from its matrix.
The compression argument must rule out the entire open interval `(1,17/16)`. -/
theorem witness_spectral_location :
    spectrum ℝ witnessMatrix ⊆ Set.Icc 0 1 ∪ Set.Ici witnessA := by
  exact witness_spectral_location_proved

/-- Scalar minorant on precisely the proved spectral set. This assertion is
not operator monotonicity of the kink function. -/
theorem minorant_scalar (x : ℝ) (hx : 0 ≤ x) (hgap : x ≤ 1 ∨ witnessA ≤ x) :
    minorantFunction x ≤ witnessFunction x := by
  exact minorant_scalar_proved x hx hgap

/-- Polynomial identification and pointwise-on-spectrum CFC order for the
actual witness, with no assumption of the desired spectral gap or inequality. -/
theorem minorant_functional_calculus :
    functionalCalculus minorantFunction witnessMatrix = minorantMatrix witnessMatrix ∧
      minorantMatrix witnessMatrix ≤ functionalCalculus witnessFunction witnessMatrix := by
  exact minorant_functional_calculus_proved

/-- Actual fourth eigenvalue and all exact truncation identities for EVERY
permitted eigenbasis of both witness matrices. No preferred truncation is substituted. -/
theorem witness_tail_data
    (dA : OrderedSpectralData witnessMatrix)
    (dAhat : OrderedSpectralData witnessApproximation) :
    spectralNorm (witnessMatrix - witnessApproximation) = witnessT ∧
    dA.eigenvalues 3 = witnessT ∧
    truncation dAhat 3 = witnessApproximation ∧
    functionTruncation dAhat witnessFunction 3 =
      functionalCalculus witnessFunction witnessApproximation ∧
    spectralNorm (witnessMatrix - truncation dA 3) = witnessT ∧
    spectralNorm (functionalCalculus witnessFunction witnessMatrix -
      functionTruncation dA witnessFunction 3) = witnessT := by
  exact witness_tail_data_proved dA dAhat

/-- Exact matrix-vector and rational equalities, including the actual
minorant Rayleigh value. Their numerical constants are not input assumptions. -/
theorem witness_rational_certificate :
    witnessVector ⬝ᵥ witnessVector = 26 ∧
    witnessVector ⬝ᵥ (witnessF *ᵥ witnessVector) = 14912 / 585 ∧
    matrixK witnessMatrix *ᵥ witnessVector = witnessKVector ∧
    witnessKVector ⬝ᵥ witnessKVector =
      1800760572753083906132034496291 / 1019907849866242673982515970048000 ∧
    functionalCalculus witnessFunction witnessApproximation = witnessApproximationImage ∧
    witnessVector ⬝ᵥ
      ((minorantMatrix witnessMatrix -
        functionalCalculus witnessFunction witnessApproximation) *ᵥ witnessVector) =
      26 * witnessT * (1 + witnessGap) := by
  exact witness_rational_certificate_proved

/-- The material singleton certificate required from explicit kernel LeanCert.
Its proved term must feed the strict Rayleigh comparison and final negation. -/
theorem numerical_gap_positive : 0 < witnessGap := by
  exact numerical_gap_positive_proved

/-- The complete universal implication fails at epsilon zero, for every
allowed decomposition of this admissible source pair. -/
theorem counterexample
    (dA : OrderedSpectralData witnessMatrix)
    (dAhat : OrderedSpectralData witnessApproximation) :
    spectralNorm (witnessMatrix - truncation dAhat 3) ≤
      spectralNorm (witnessMatrix - truncation dA 3) ∧
    ¬ (spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dAhat witnessFunction 3) ≤
        spectralNorm (functionalCalculus witnessFunction witnessMatrix -
          functionTruncation dA witnessFunction 3)) := by
  exact counterexample_proved dA dAhat

/-- Unconditional negation of the complete original all-dimension,
all-function, all-parameter, all-eigenbasis assertion. -/
theorem not_concaveSpectralTransferConjecture : ¬ ConcaveSpectralTransferConjecture := by
  exact not_concaveSpectralTransferConjecture_proved

#assert_trust kernel orderedSpectral_exists
#print axioms orderedSpectral_exists
#assert_trust kernel orderedSpectral_semantics
#print axioms orderedSpectral_semantics
#assert_trust kernel functionalCalculus_spectral
#print axioms functionalCalculus_spectral
#assert_trust kernel spectral_tail_norms
#print axioms spectral_tail_norms
#assert_trust kernel operator_rayleigh_bound
#print axioms operator_rayleigh_bound
#assert_trust kernel witness_data
#print axioms witness_data
#assert_trust kernel witness_spectral_location
#print axioms witness_spectral_location
#assert_trust kernel minorant_scalar
#print axioms minorant_scalar
#assert_trust kernel minorant_functional_calculus
#print axioms minorant_functional_calculus
#assert_trust kernel witness_tail_data
#print axioms witness_tail_data
#assert_trust kernel witness_rational_certificate
#print axioms witness_rational_certificate
#assert_trust kernel numerical_gap_positive
#print axioms numerical_gap_positive
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_concaveSpectralTransferConjecture
#print axioms not_concaveSpectralTransferConjecture

end NLA.RA08
