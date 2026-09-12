/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's rational counterexample to MI-06.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI06.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped ComplexOrder Matrix MatrixOrder

namespace NLA.MI06

/-- The modulus is the genuine positive square root for every complex matrix. -/
theorem modulus_eq_sqrt {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef := by
  exact modulus_eq_sqrt_proved X

/-- All exact CFC values and rank-one decompositions are conclusions, not assumptions. -/
theorem witness_moduli :
    matrixModulus witnessA = rightModulusA ∧
    matrixModulus witnessA.conjTranspose = axialModulus ∧
    matrixModulus witnessB = axialModulus ∧
    matrixModulus witnessB.conjTranspose = leftModulusB ∧
    matrixModulus (witnessA + witnessB) = rightModulusSum ∧
    matrixModulus (witnessA + witnessB).conjTranspose = leftModulusSum ∧
    symmetricModulus witnessA = symmetricA ∧
    symmetricModulus witnessB = symmetricB ∧
    symmetricModulus (witnessA + witnessB) = symmetricSum ∧
    symmetricA = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionA -
      (1 / 8 : ℂ) • missingA ∧
    symmetricB = (1 / 8 : ℂ) • 1 + (1 / 10 : ℂ) • rankOne directionB -
      (1 / 8 : ℂ) • missingB := by
  exact witness_moduli_proved

/-- Every two complex vectors in dimension three have a nonzero orthogonal vector. -/
theorem two_vector_orthogonal (a b : Fin 3 → ℂ) :
    ∃ w : Fin 3 → ℂ, 0 < squaredLength w ∧
      star a ⬝ᵥ w = 0 ∧ star b ⬝ᵥ w = 0 := by
  exact two_vector_orthogonal_proved a b

/-- Homogeneous quadratic bounds for every pair of complex unitaries.
All forms use the actual arithmetic CFC moduli, rather than assumed matrix tables. -/
theorem witness_quadratic_bounds (U V : Matrix.unitaryGroup (Fin 3) ℂ) :
    ∃ w : Fin 3 → ℂ, 0 < squaredLength w ∧
      star ((U : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionA) ⬝ᵥ w = 0 ∧
      star ((V : Matrix (Fin 3) (Fin 3) ℂ) *ᵥ directionB) ⬝ᵥ w = 0 ∧
      (3 / 8 : ℝ) * squaredLength w ≤
        quadraticForm (symmetricModulus (witnessA + witnessB)) w ∧
      quadraticForm (unitaryConjugate U (symmetricModulus witnessA)) w ≤
        (1 / 8 : ℝ) * squaredLength w ∧
      quadraticForm (unitaryConjugate V (symmetricModulus witnessB)) w ≤
        (1 / 8 : ℝ) * squaredLength w := by
  exact witness_quadratic_bounds_proved U V

/-- The fixed rational pair defeats every pair of complex unitaries in PSD order. -/
theorem counterexample :
    ∀ U V : Matrix.unitaryGroup (Fin 3) ℂ,
      ¬ (symmetricModulus (witnessA + witnessB) ≤
        (Real.sqrt 2 : ℂ) •
          (unitaryConjugate U (symmetricModulus witnessA) +
            unitaryConjugate V (symmetricModulus witnessB))) := by
  exact counterexample_proved

/-- The complete original universal assertion is false. -/
theorem not_dominationConjecture : ¬ DominationConjecture := by
  exact not_dominationConjecture_proved

#assert_trust kernel modulus_eq_sqrt
#assert_trust kernel witness_moduli
#assert_trust kernel two_vector_orthogonal
#assert_trust kernel witness_quadratic_bounds
#assert_trust kernel counterexample
#assert_trust kernel not_dominationConjecture

#print axioms modulus_eq_sqrt
#print axioms witness_moduli
#print axioms two_vector_orthogonal
#print axioms witness_quadratic_bounds
#print axioms counterexample
#print axioms not_dominationConjecture

end NLA.MI06
