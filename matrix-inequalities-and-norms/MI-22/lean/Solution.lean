/- Complete solution of the frozen MI-22 statement boundary.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
The witness is an exact rational adaptation of Matthew J. Colbrook's method. -/
import NLA.MI22.Proof

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI22

/-- Genuine sorted singular-value semantics, including all dimensions and
multiplicities through Mathlib's actual adjoint-composition eigenvalues. -/
theorem singular_values_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    (∀ j : ℕ, 0 ≤ singularValue A j) ∧
    Antitone (singularValue A) ∧
    (∀ j : ℕ, n ≤ j → singularValue A j = 0) ∧
    (∀ i : Fin n, singularValue A i =
      Real.sqrt ((Matrix.toEuclideanLin A).isSymmetric_adjoint_comp_self.eigenvalues
        (by simp) i)) ∧
    singularValue A 0 = operatorNorm A := by
  exact singular_values_semantics_proved hn A

/-- Actual CFC agrees with the principal spectral power for every positive
definite complex matrix and every real exponent, not merely for the witness. -/
theorem spectral_power_semantics {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    spectralPower A r =
      (hA.isHermitian.eigenvectorUnitary : Mat n) *
        Matrix.diagonal (fun i => (((hA.isHermitian.eigenvalues i) ^ r : ℝ) : ℂ)) *
        (hA.isHermitian.eigenvectorUnitary : Mat n).conjTranspose := by
  exact spectral_power_semantics_proved A hA r

/-- The actual operator/Frobenius inequality and action-coordinate bound for
arbitrary complex matrices and arbitrary Euclidean vectors. -/
theorem euclidean_norm_bounds {n : ℕ} (A : Mat n) :
    operatorNorm A ^ 2 ≤ frobeniusSquared A ∧
    (∀ x : EuclideanSpace ℂ (Fin n), ∀ i : Fin n,
      ‖(Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x) i‖ ≤
        operatorNorm A * ‖x‖) := by
  exact euclidean_norm_bounds_proved A

/-- All finite certificates are conclusions about the actual rational matrices.
No factorization, positivity, norm, or tested entry is assumed as a premise. -/
theorem witness_rational_data :
    witnessT = witnessLDL * witnessPivots * witnessLDL.conjTranspose ∧
    witnessA = Matrix.diagonal (![256, 1 / 256, 1] : Fin 3 → ℂ) ∧
    witnessT.PosDef ∧ witnessA.PosDef ∧ witnessB.PosDef ∧
    ‖witnessVector‖ = 1 ∧
    witnessB.trace.re < (4 : ℝ) ^ (8 : ℕ) ∧
    44000 < witnessTestValue ∧
    frobeniusSquared (witnessA * witnessB) < (10500 : ℝ) ^ (2 : ℕ) := by
  exact witness_rational_data_proved

/-- Every principal-power identity and root-norm bound used in the exact
reduction. In particular, witnessRoot is the actual root, never a proxy. -/
theorem witness_principal_powers :
    spectralPower witnessA (1 / 2) = witnessD ∧
    spectralPower witnessA (-1 / 2) = witnessDInv ∧
    spectralPower witnessA (1 / 8) = witnessAOneEighth ∧
    spectralPower witnessA (5 / 8) = witnessAFiveEighths ∧
    spectralPower (witnessDInv * witnessB * witnessDInv) (1 / 8) = witnessT ∧
    weightedMean witnessA witnessB (1 / 8) = witnessD * witnessT * witnessD ∧
    witnessRoot.PosDef ∧ witnessRoot ^ (8 : ℕ) = witnessB ∧
    spectralPower witnessB (7 / 8) * witnessRoot = witnessB ∧
    leftProduct witnessA witnessB (1 / 8) * witnessRoot = witnessN ∧
    operatorNorm witnessRoot < 4 := by
  exact witness_principal_powers_proved

/-- Strict estimates for the actual matrices in the canonical target. -/
theorem witness_operator_gap :
    operatorNorm (witnessA * witnessB) < 10500 ∧
    11000 < operatorNorm (leftProduct witnessA witnessB (1 / 8)) := by
  exact witness_operator_gap_proved

/-- A fully admissible complex positive-definite instance with a strict first
singular-value reversal, hence failure of the full original log-majorization. -/
theorem counterexample :
    witnessA.PosDef ∧ witnessB.PosDef ∧
    (0 : ℝ) ≤ 1 / 8 ∧ (1 / 8 : ℝ) ≤ 1 ∧
    singularValue (witnessA * witnessB) 0 <
      singularValue (leftProduct witnessA witnessB (1 / 8)) 0 ∧
    ¬ SingularLogMajorized (leftProduct witnessA witnessB (1 / 8))
      (witnessA * witnessB) := by
  exact counterexample_proved

/-- Full negation of the entire canonical statement, with no restricted
parameter range, numerical substitute, or extra assumption. -/
theorem not_weightedLogMajorizationConjecture : ¬ WeightedLogMajorizationConjecture := by
  exact not_weightedLogMajorizationConjecture_proved

#assert_trust kernel singular_values_semantics
#print axioms singular_values_semantics
#assert_trust kernel spectral_power_semantics
#print axioms spectral_power_semantics
#assert_trust kernel euclidean_norm_bounds
#print axioms euclidean_norm_bounds
#assert_trust kernel witness_rational_data
#print axioms witness_rational_data
#assert_trust kernel witness_principal_powers
#print axioms witness_principal_powers
#assert_trust kernel witness_operator_gap
#print axioms witness_operator_gap
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_weightedLogMajorizationConjecture
#print axioms not_weightedLogMajorizationConjecture

end NLA.MI22
