/- Exact witness sums and optimality for Matthew J. Colbrook's MI-03 theorem.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted; Apache 2.0. -/
import NLA.MI03.Witness
import NLA.MI03.UpperBound

set_option autoImplicit false
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MI03

theorem witness_matrix (k : ℕ) (j : Fin k) : witness k j =
    !![1 / 2, ((Real.sqrt 3 : ℝ) : ℂ) / 2 * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ));
       0, 0] := by
  ext i l
  fin_cases i <;> fin_cases l <;>
    norm_num [witness, outerProduct, Matrix.vecMulVec_apply, firstVector, witnessVector,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Complex.star_def, map_ofNat]

theorem witness_modulus_matrix (k : ℕ) (hk : 2 ≤ k) (j : Fin k) :
    matrixModulus (witness k j) =
      !![1 / 4, ((Real.sqrt 3 : ℝ) : ℂ) / 4 * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ));
         ((Real.sqrt 3 : ℝ) : ℂ) / 4 * rootOfUnity k ^ (j : ℕ), 3 / 4] := by
  rw [witness_modulus k hk j]
  have hr : rootOfUnity k ^ (j : ℕ) * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ)) = 1 := by
    simpa only [Complex.star_def] using root_power_star k hk j
  ext i l
  fin_cases i <;> fin_cases l
  all_goals norm_num [outerProduct, Matrix.vecMulVec_apply, witnessVector,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail,
    Complex.star_def, map_mul, map_div₀, map_ofNat, map_one, Complex.conj_ofReal]
  · ring
  · ring
  · calc
      _ = (((Real.sqrt 3 : ℝ) : ℂ) ^ 2) / 4 *
          (rootOfUnity k ^ (j : ℕ) * (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ))) := by rw [map_pow]; ring
      _ = 3 / 4 := by rw [sqrt_three_sq, hr]; ring

theorem root_conjugate_sum (k : ℕ) (hk : 2 ≤ k) :
    (∑ j : Fin k, (starRingEnd ℂ) (rootOfUnity k ^ (j : ℕ))) = 0 := by
  rw [← map_sum, (root_of_unity_data_proved k hk).2, map_zero]

theorem conjugate_root_power_sum (k : ℕ) (hk : 2 ≤ k) :
    (∑ j : Fin k, ((starRingEnd ℂ) (rootOfUnity k)) ^ (j : ℕ)) = 0 := by
  simpa only [map_pow] using root_conjugate_sum k hk

theorem witness_sum (k : ℕ) (hk : 2 ≤ k) :
    summandSum (witness k) = ((k : ℂ) / 2) • firstProjection := by
  rw [firstProjection_diagonal]
  ext i l
  fin_cases i <;> fin_cases l
  all_goals simp [summandSum, Matrix.sum_apply, witness_matrix,
    firstVector, Matrix.smul_apply, smul_eq_mul,
    ← Finset.mul_sum, conjugate_root_power_sum k hk]
  all_goals try ring

theorem witness_modulus_sum (k : ℕ) (hk : 2 ≤ k) :
    modulusSum (witness k) = witnessModulusSum k := by
  ext i l
  fin_cases i <;> fin_cases l
  all_goals simp [modulusSum, Matrix.sum_apply, witness_modulus_matrix k hk,
    witnessModulusSum, ← Finset.mul_sum,
    conjugate_root_power_sum k hk, (root_of_unity_data_proved k hk).2]
  all_goals try ring

theorem witness_sum_posSemidef (k : ℕ) (hk : 2 ≤ k) :
    (summandSum (witness k)).PosSemidef := by
  rw [witness_sum k hk]
  exact (outerProduct_posSemidef firstVector).smul (by positivity)

theorem witness_sum_modulus (k : ℕ) (hk : 2 ≤ k) :
    matrixModulus (summandSum (witness k)) = summandSum (witness k) := by
  exact CFC.abs_of_nonneg _ (witness_sum_posSemidef k hk).nonneg

theorem witness_difference (k : ℕ) (hk : 2 ≤ k) :
    matrixModulus (summandSum (witness k)) - modulusSum (witness k) =
      witnessDifference k := by
  rw [witness_sum_modulus k hk, witness_sum k hk, witness_modulus_sum k hk,
    firstProjection_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [witnessModulusSum, witnessDifference, firstVector,
      Matrix.smul_apply, smul_eq_mul] <;> ring

end NLA.MI03
