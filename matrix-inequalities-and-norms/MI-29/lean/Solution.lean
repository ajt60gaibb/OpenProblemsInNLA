/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-29.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI29.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped ComplexOrder MatrixOrder

namespace NLA.MI29

/-- Spectral powers agree with actual ring powers, including exponent zero. -/
theorem spectralPower_natCast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (r : ℕ) :
    spectralPower A (r : ℝ) = A ^ r := by
  exact spectralPower_natCast_proved A hA r

/-- The analytic square-root bridge is proved for the genuine matrix modulus. -/
theorem modulus_power_eight {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    matrixModulus X = CFC.sqrt (X.conjTranspose * X) ∧
    (matrixModulus X).PosSemidef ∧
    spectralPower (matrixModulus X) 8 = (X.conjTranspose * X) ^ (4 : ℕ) := by
  exact modulus_power_eight_proved X

/-- The comparison really is between positive real determinants. -/
theorem comparison_positive_real {n : ℕ} (hn : 1 ≤ n)
    (A B : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (hB : B.IsHermitian) (hBinv : IsUnit B)
    (k p : ℝ) (hk : 0 ≤ k) (hp : 0 ≤ p) :
    (leftDet A B k p).im = 0 ∧ 0 < (leftDet A B k p).re ∧
    (rightDet A B k p).im = 0 ∧ 0 < (rightDet A B k p).re := by
  exact comparison_positive_real_proved hn A B hA hB hBinv k p hk hp

/-- All witness hypotheses, analytic reductions, and determinant values are consequences. -/
theorem counterexample :
    witnessA.PosDef ∧ witnessB.IsHermitian ∧ IsUnit witnessB ∧
    witnessB.det = (-1 / 125 : ℂ) ∧
    ¬ witnessB.PosSemidef ∧ ¬ (-witnessB).PosSemidef ∧
    spectralPower witnessA 6 = witnessA ^ (6 : ℕ) ∧
    spectralPower (matrixModulus (witnessA * witnessB)) 8 =
      (witnessB * witnessA ^ (2 : ℕ) * witnessB) ^ (4 : ℕ) ∧
    spectralPower (matrixModulus (witnessB * witnessA)) 8 =
      (witnessA * witnessB ^ (2 : ℕ) * witnessA) ^ (4 : ℕ) ∧
    leftDet witnessA witnessB 6 8 =
      (136990346414301954149 / 61035156250000000000 : ℂ) ∧
    rightDet witnessA witnessB 6 8 =
      (4537743716162890657 / 1907348632812500000 : ℂ) ∧
    rightDet witnessA witnessB 6 8 - leftDet witnessA witnessB 6 8 =
      (21036678407451 / 156250000000000 : ℂ) ∧
    leftDet witnessA witnessB 6 8 < rightDet witnessA witnessB 6 8 := by
  exact counterexample_proved

/-- One admissible witness refutes the complete all-parameter conjecture. -/
theorem not_modulusDeterminantConjecture : ¬ ModulusDeterminantConjecture := by
  exact not_modulusDeterminantConjecture_proved

#assert_trust kernel spectralPower_natCast
#assert_trust kernel modulus_power_eight
#assert_trust kernel comparison_positive_real
#assert_trust kernel counterexample
#assert_trust kernel not_modulusDeterminantConjecture

#print axioms spectralPower_natCast
#print axioms modulus_power_eight
#print axioms comparison_positive_real
#print axioms counterexample
#print axioms not_modulusDeterminantConjecture

end NLA.MI29
