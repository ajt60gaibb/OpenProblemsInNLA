/- Full proof exports matching the independently approved Challenge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
Mathematical proof: Matthew J. Colbrook. AI-assisted formalization. -/
import NLA.MI03.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder
noncomputable section

namespace NLA.MI03

/-- Actual positive modulus and its norm, for arbitrary complex matrices. -/
theorem modulus_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    (matrixModulus A).PosSemidef ∧
    matrixModulus A * matrixModulus A = A.conjTranspose * A ∧
    operatorNorm (matrixModulus A) = operatorNorm A := by
  exact modulus_semantics_proved hn A

/-- Contraction control in genuine PSD order, including singular and zero inputs. -/
theorem contraction_modulus {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : operatorNorm A ≤ 1) :
    ((1 : Mat n) - matrixModulus A).PosSemidef ∧
    (matrixModulus A - matrixModulus A * matrixModulus A).PosSemidef := by
  exact contraction_modulus_proved hn A hA

/-- Exact positive-square decomposition. The finite sum identity and the two
unconditional positivity assertions are conclusions, not supplied certificates. -/
theorem positive_decomposition {n k : ℕ} (hn : 1 ≤ n) (hk : 2 ≤ k)
    (A : Fin k → Mat n) :
    (k : ℂ) • errorGap A ((k : ℝ) / 4) =
      (k : ℂ) • (∑ j, (matrixModulus (A j) -
        matrixModulus (A j) * matrixModulus (A j))) +
        pairVariance A + shiftedSquare A ∧
    (pairVariance A).PosSemidef ∧ (shiftedSquare A).PosSemidef := by
  exact positive_decomposition_proved hn hk A

/-- Complete dimension-independent upper bound; no external inequality premise. -/
theorem universal_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    AdmissibleConstant k ((k : ℝ) / 4) := by
  exact universal_upper_bound_proved k hk

/-- Exact roots-of-unity facts for every summand count, without numerical phases. -/
theorem root_of_unity_data (k : ℕ) (hk : 2 ≤ k) :
    ‖rootOfUnity k‖ = 1 ∧
    (∑ j : Fin k, rootOfUnity k ^ (j : ℕ)) = 0 := by
  exact root_of_unity_data_proved k hk

/-- The full dimension-two construction on actual matrices and Euclidean vectors. -/
theorem sharpness_witness (k : ℕ) (hk : 2 ≤ k) :
    (∀ j : Fin k, ‖WithLp.toLp 2 (witnessVector k j)‖ = (1 : ℝ)) ∧
    (∀ j : Fin k, operatorNorm (witness k j) = 1) ∧
    (∀ j : Fin k, matrixModulus (witness k j) =
      outerProduct (witnessVector k j) (witnessVector k j)) ∧
    summandSum (witness k) = ((k : ℂ) / 2) • firstProjection ∧
    modulusSum (witness k) = witnessModulusSum k ∧
    matrixModulus (summandSum (witness k)) - modulusSum (witness k) =
      witnessDifference k := by
  exact sharpness_witness_proved k hk

/-- Attainment and the actual infimum for every k≥2, so the infimum is never
used through an empty-set or unbounded-below convention. -/
theorem sharp_constant (k : ℕ) (hk : 2 ≤ k) :
    IsLeast (admissibleConstants k) ((k : ℝ) / 4) ∧
    sharpConstant k = (k : ℝ) / 4 := by
  exact sharp_constant_proved k hk

/-- Complete affirmative answer to the original every-odd-k conjecture. -/
theorem odd_contraction_conjecture : OddContractionConjecture := by
  exact odd_contraction_conjecture_proved

#assert_trust kernel modulus_semantics
#print axioms modulus_semantics
#assert_trust kernel contraction_modulus
#print axioms contraction_modulus
#assert_trust kernel positive_decomposition
#print axioms positive_decomposition
#assert_trust kernel universal_upper_bound
#print axioms universal_upper_bound
#assert_trust kernel root_of_unity_data
#print axioms root_of_unity_data
#assert_trust kernel sharpness_witness
#print axioms sharpness_witness
#assert_trust kernel sharp_constant
#print axioms sharp_constant
#assert_trust kernel odd_contraction_conjecture
#print axioms odd_contraction_conjecture

end NLA.MI03
