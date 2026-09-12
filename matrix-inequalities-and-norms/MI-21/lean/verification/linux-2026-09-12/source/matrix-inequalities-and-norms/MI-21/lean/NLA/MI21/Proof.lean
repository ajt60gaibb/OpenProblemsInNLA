/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to MI-21.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.MI21.Definitions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import LeanCert.Tactic.IntervalAuto.PointIneq

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section

namespace NLA.MI21

/-- The explicit norm in the frozen definition is precisely Mathlib's L2 operator norm. -/
lemma operatorNorm_eq {n : ℕ} (X : Mat n) : operatorNorm X = ‖X‖ := rfl

theorem operatorNorm_isUnitaryInvariant_proved (n : ℕ) :
    IsUnitaryInvariantNorm (operatorNorm (n := n)) := by
  simp only [IsUnitaryInvariantNorm, operatorNorm_eq]
  refine ⟨fun X => norm_nonneg X, fun X => norm_eq_zero,
    fun X Y => norm_add_le X Y, fun z X => norm_smul z X, ?_⟩
  intro U V X hU₁ hU₂ hV₁ hV₂
  have hU : U ∈ unitary (Mat n) := Unitary.mem_iff.mpr ⟨hU₁, hU₂⟩
  have hV : V ∈ unitary (Mat n) := Unitary.mem_iff.mpr ⟨hV₁, hV₂⟩
  rw [CStarRing.norm_mul_mem_unitary _ hV, CStarRing.norm_mem_unitary_mul _ hU]

lemma spectralPower_nat {n : ℕ} (A : Mat n) (hA : A.PosSemidef) (r : ℕ) :
    spectralPower A (r : ℝ) = A ^ r := CFC.rpow_natCast A r hA.nonneg

lemma rpow_half_eq_sqrt {n : ℕ} (A : Mat n) :
    CFC.rpow A (1 / 2) = CFC.sqrt A := CFC.sqrt_eq_rpow.symm

lemma spectralPower_sq_half {n : ℕ} (A : Mat n) (hA : A.PosSemidef) :
    spectralPower (A ^ (2 : ℕ)) (1 / 2) = A := by
  change CFC.rpow (A ^ (2 : ℕ)) (1 / 2) = A
  rw [rpow_half_eq_sqrt, CFC.sqrt_sq A hA.nonneg]

lemma spectralPower_posDef {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℝ) :
    (spectralPower A r).PosDef :=
  (IsStrictlyPositive.rpow A r hA.isStrictlyPositive).posDef

/-- A positive Riccati solution is the actual CFC geometric mean. The inverse
certificate `A*K=1` and the equation `X*K*X=B` are checked independently below. -/
lemma geometricMean_eq_of_riccati {n : ℕ} (A B K X : Mat n)
    (hA : A.PosDef) (hX : X.PosSemidef) (hAK : A * K = 1)
    (hXX : X * K * X = B) : geometricMean A B (1 / 2) = X := by
  let H := CFC.rpow A (1 / 2)
  let J := CFC.rpow A (-1 / 2)
  have hHJ : H * J = 1 := by
    have ht : CFC.rpow A (1 / 2) * CFC.rpow A (-(1 / 2)) = 1 :=
      CFC.rpow_mul_rpow_neg (1 / 2) hA.isStrictlyPositive
    simpa only [H, J, neg_div] using ht
  have hJH : J * H = 1 := by
    have ht : CFC.rpow A (-(1 / 2)) * CFC.rpow A (1 / 2) = 1 :=
      CFC.rpow_neg_mul_rpow (1 / 2) hA.isStrictlyPositive
    simpa only [H, J, neg_div] using ht
  have hIA : CFC.rpow A (-1) * A = 1 := by
    simpa [CFC.rpow_one A hA.posSemidef.nonneg] using
      CFC.rpow_neg_mul_rpow (1 : ℝ) hA.isStrictlyPositive
  have hK : CFC.rpow A (-1) = K := by
    calc
      CFC.rpow A (-1) = CFC.rpow A (-1) * (A * K) := by rw [hAK, mul_one]
      _ = K := by rw [← mul_assoc, hIA, one_mul]
  have hJJ : J * J = K := by
    dsimp [J]
    rw [← CFC.rpow_add hA.isUnit]
    norm_num
    exact hK
  have hZ : (J * X * J).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (conjugate_nonneg_of_nonneg hX.nonneg (CFC.rpow_nonneg (a := A) (y := -1 / 2)))
  have hZsq : (J * X * J) * (J * X * J) = J * B * J := by
    calc
      (J * X * J) * (J * X * J) = J * (X * (J * J) * X) * J := by
        simp only [mul_assoc]
      _ = J * B * J := by rw [hJJ, hXX]
  have hsqrt : CFC.sqrt (J * B * J) = J * X * J := CFC.sqrt_unique hZsq hZ.nonneg
  change H * CFC.rpow (J * B * J) (1 / 2) * H = X
  rw [rpow_half_eq_sqrt, hsqrt]
  calc
    H * (J * X * J) * H = (H * J) * X * (J * H) := by simp only [mul_assoc]
    _ = X := by rw [hHJ, hJH, one_mul, mul_one]

/-- A scaled rational Riccati certificate computes the squared actual mean.
Only the positive scalar square root is introduced, and its square cancels. -/
lemma mean_squared_of_scaled_riccati {n : ℕ} (A B K N : Mat n) (h : ℝ)
    (hA : A.PosDef) (hN : N.PosSemidef) (hh : 0 < h)
    (hAK : A * K = 1) (hNN : N * K * N = (h : ℂ) • B) :
    spectralPower (geometricMean A B (1 / 2)) 2 = (1 / h : ℂ) • N ^ (2 : ℕ) := by
  let c : ℂ := ((1 / Real.sqrt h : ℝ) : ℂ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg h))
  have hc2 : c * c = (1 / h : ℂ) := by
    have hr : (1 / Real.sqrt h) ^ (2 : ℕ) = 1 / h := by
      rw [_root_.one_div_pow, Real.sq_sqrt hh.le]
    dsimp [c]
    exact_mod_cast (show (1 / Real.sqrt h) * (1 / Real.sqrt h) = 1 / h by
      simpa only [pow_two] using hr)
  have hX : (c • N).PosSemidef := hN.smul hc
  have hric : (c • N) * K * (c • N) = B := by
    calc
      (c • N) * K * (c • N) = (c * c) • (N * K * N) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = (1 / h : ℂ) • ((h : ℂ) • B) := by rw [hc2, hNN]
      _ = B := by
        rw [smul_smul]
        simp [hh.ne']
  have hp : spectralPower (c • N) 2 = (c • N) ^ (2 : ℕ) :=
    spectralPower_nat (c • N) hX 2
  rw [geometricMean_eq_of_riccati A B K (c • N) hA hX hAK hric, hp]
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul, hc2]

lemma posDef_pow {n : ℕ} (A : Mat n) (hA : A.PosDef) (r : ℕ) :
    (A ^ r).PosDef := (hA.posSemidef.pow r).posDef_iff_isUnit.mpr (hA.isUnit.pow r)

lemma witnessC_posDef : witnessC.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

lemma witnessE_posDef : witnessE.PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [Complex.pos_iff]

lemma witnessS_hermitian : witnessS.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessS, Matrix.conjTranspose_apply]

lemma witnessS_involution : witnessS * witnessS = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessS, Matrix.mul_apply, Fin.sum_univ_two]

lemma witnessS_isUnit : IsUnit witnessS :=
  ⟨⟨witnessS, witnessS, witnessS_involution, witnessS_involution⟩, rfl⟩

lemma witness_conjugate_posDef (X : Mat 2) (hX : X.PosDef) :
    (witnessS * X * witnessS).PosDef := by
  simpa only [witnessS_hermitian.eq] using
    hX.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit witnessS_isUnit)

lemma witness_conjugate_posSemidef (X : Mat 2) (hX : X.PosSemidef) :
    (witnessS * X * witnessS).PosSemidef := by
  simpa only [witnessS_hermitian.eq] using hX.conjTranspose_mul_mul_same witnessS

lemma witness_conjugate_sq (X : Mat 2) :
    (witnessS * X * witnessS) ^ (2 : ℕ) = witnessS * X ^ (2 : ℕ) * witnessS := by
  calc
    (witnessS * X * witnessS) ^ (2 : ℕ) =
        witnessS * X * (witnessS * witnessS) * X * witnessS := by
      simp only [pow_two, mul_assoc]
    _ = witnessS * X ^ (2 : ℕ) * witnessS := by
      rw [witnessS_involution, mul_one]
      simp only [pow_two, mul_assoc]

lemma witness_inputs_posDef (i : Fin 2) :
    (witnessA i).PosDef ∧ (witnessB i).PosDef := by
  fin_cases i
  · exact ⟨posDef_pow witnessC witnessC_posDef 2,
      witness_conjugate_posDef _ (posDef_pow witnessE witnessE_posDef 2)⟩
  · exact ⟨posDef_pow witnessE witnessE_posDef 2,
      witness_conjugate_posDef _ (posDef_pow witnessC witnessC_posDef 2)⟩

lemma witness_sum_A : (∑ i, witnessA i) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessC, witnessE, Matrix.diagonal_pow, Fin.sum_univ_two,
      Matrix.diagonal_apply]

lemma witness_sum_B : (∑ i, witnessB i) = 1 := by
  have hCE : witnessC ^ (2 : ℕ) + witnessE ^ (2 : ℕ) = 1 := by
    simpa only [witnessA, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] using
      witness_sum_A
  simp only [witnessB, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← add_mul, ← mul_add, add_comm (witnessE ^ (2 : ℕ)), hCE, mul_one,
    witnessS_involution]

private def inverseC : Mat 2 := Matrix.diagonal (![37 / 12, 29 / 21] : Fin 2 → ℂ)
private def inverseE : Mat 2 := Matrix.diagonal (![37 / 35, 29 / 20] : Fin 2 → ℂ)
private def meanScale : ℝ := 61697295 / 8682716
private def meanNumerator : Mat 2 :=
  witnessS * witnessE * witnessS + (5 / 3 : ℂ) • witnessC
private def secondMeanNumerator : Mat 2 := witnessS * meanNumerator * witnessS

private lemma meanScale_positive : 0 < meanScale := by norm_num [meanScale]

private lemma meanNumerator_posSemidef : meanNumerator.PosSemidef :=
  (witness_conjugate_posSemidef _ witnessE_posDef.posSemidef).add
    (witnessC_posDef.posSemidef.smul (by norm_num [Complex.nonneg_iff] : (0 : ℂ) ≤ 5 / 3))

private lemma secondMeanNumerator_posSemidef : secondMeanNumerator.PosSemidef :=
  witness_conjugate_posSemidef meanNumerator meanNumerator_posSemidef

private lemma inverseC_certificate : witnessC * inverseC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessC, inverseC, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

private lemma inverseE_certificate : witnessE * inverseE = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessE, inverseE, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

private lemma meanNumerator_explicit :
    meanNumerator = (1 / 310097 : ℂ) • !![443355, 33000; 33000, 605715] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [meanNumerator, witnessS, witnessE, witnessC, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

private lemma secondMeanNumerator_explicit :
    secondMeanNumerator = (1 / 310097 : ℂ) • !![506715, -85800; -85800, 542355] := by
  rw [secondMeanNumerator, meanNumerator_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessS, Matrix.mul_apply, Fin.sum_univ_two]

/-- First exact Riccati certificate; the inverse and ordered products are actual matrices. -/
private lemma first_riccati_certificate :
    meanNumerator * inverseC * meanNumerator =
      (meanScale : ℂ) • (witnessS * witnessE * witnessS) := by
  rw [meanNumerator_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [meanScale, inverseC, witnessS, witnessE, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

/-- The second mean is separately certified, so no unproved covariance or symmetry rule enters. -/
private lemma second_riccati_certificate :
    secondMeanNumerator * inverseE * secondMeanNumerator =
      (meanScale : ℂ) • (witnessS * witnessC * witnessS) := by
  rw [secondMeanNumerator_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [meanScale, inverseE, witnessS, witnessC, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply, Matrix.vecMul, dotProduct]

private lemma first_actual_mean_squared :
    spectralPower (geometricMean witnessC (witnessS * witnessE * witnessS) (1 / 2)) 2 =
      (1 / meanScale : ℂ) • meanNumerator ^ (2 : ℕ) :=
  mean_squared_of_scaled_riccati witnessC _ inverseC meanNumerator meanScale
    witnessC_posDef meanNumerator_posSemidef meanScale_positive
    inverseC_certificate first_riccati_certificate

private lemma second_actual_mean_squared :
    spectralPower (geometricMean witnessE (witnessS * witnessC * witnessS) (1 / 2)) 2 =
      (1 / meanScale : ℂ) • secondMeanNumerator ^ (2 : ℕ) :=
  mean_squared_of_scaled_riccati witnessE _ inverseE secondMeanNumerator meanScale
    witnessE_posDef secondMeanNumerator_posSemidef meanScale_positive
    inverseE_certificate second_riccati_certificate

lemma witness_input_roots :
    spectralPower (witnessA 0) (1 / 2) = witnessC ∧
    spectralPower (witnessA 1) (1 / 2) = witnessE ∧
    spectralPower (witnessB 0) (1 / 2) = witnessS * witnessE * witnessS ∧
    spectralPower (witnessB 1) (1 / 2) = witnessS * witnessC * witnessS := by
  refine ⟨spectralPower_sq_half witnessC witnessC_posDef.posSemidef,
    spectralPower_sq_half witnessE witnessE_posDef.posSemidef, ?_, ?_⟩
  · change spectralPower (witnessS * witnessE ^ (2 : ℕ) * witnessS) (1 / 2) = _
    rw [← witness_conjugate_sq]
    exact spectralPower_sq_half _ (witness_conjugate_posSemidef _ witnessE_posDef.posSemidef)
  · change spectralPower (witnessS * witnessC ^ (2 : ℕ) * witnessS) (1 / 2) = _
    rw [← witness_conjugate_sq]
    exact spectralPower_sq_half _ (witness_conjugate_posSemidef _ witnessC_posDef.posSemidef)

lemma witness_left_matrix :
    leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2 = witnessL := by
  simp only [leftMatrix, Fin.sum_univ_two]
  rw [witness_input_roots.1, witness_input_roots.2.1,
    witness_input_roots.2.2.1, witness_input_roots.2.2.2,
    first_actual_mean_squared, second_actual_mean_squared,
    meanNumerator_explicit, secondMeanNumerator_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [meanScale, witnessL, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma spectralPower_one {n : ℕ} (r : ℝ) : spectralPower (1 : Mat n) r = 1 :=
  CFC.one_rpow

lemma witness_right_matrix (p : ℝ) :
    rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p = 1 := by
  simp only [rightMatrix, witness_sum_A, witness_sum_B, spectralPower_one, mul_one]

lemma witness_vector_ne_zero : witnessVector ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 2)
  norm_num [witnessVector] at h0

lemma witness_eigenvector :
    witnessL *ᵥ witnessVector = (witnessEigenvalue : ℂ) • witnessVector := by
  ext i
  fin_cases i <;>
    norm_num [witnessL, witnessVector, witnessEigenvalue, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

/-- This retained kernel LeanCert point certificate is used by the norm bound
and strict counterexample, and hence by the complete conjecture negation. -/
lemma witness_eigenvalue_gt_one : 1 < witnessEigenvalue := by
  unfold witnessEigenvalue
  interval_decide (trust := kernel)

/-- An actual nonzero Euclidean eigenvector gives a lower bound for the actual
operator norm; no eigenvalue list or separate spectral-radius premise is needed. -/
lemma real_eigenvalue_le_operatorNorm {n : ℕ} (A : Mat n) (v : Fin n → ℂ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hv : v ≠ 0) (he : A *ᵥ v = (lam : ℂ) • v) :
    lam ≤ operatorNorm A := by
  let x : EuclideanSpace ℂ (Fin n) := WithLp.toLp 2 v
  have hx : x ≠ 0 := fun h => hv (congrArg WithLp.ofLp h)
  have hTx : Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A x = (lam : ℂ) • x := by
    simp only [x, Matrix.toEuclideanCLM_toLp, he, WithLp.toLp_smul]
  have hb := (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A).le_opNorm x
  rw [hTx, norm_smul, Complex.norm_of_nonneg hlam] at hb
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx)).mp hb

lemma witness_left_norm_lower_bound :
    witnessEigenvalue ≤ operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) := by
  rw [witness_left_matrix]
  exact real_eigenvalue_le_operatorNorm witnessL witnessVector witnessEigenvalue
    (le_of_lt (lt_trans zero_lt_one witness_eigenvalue_gt_one))
    witness_vector_ne_zero witness_eigenvector

lemma witness_right_norm (p : ℝ) :
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) = 1 := by
  rw [witness_right_matrix, operatorNorm_eq]
  exact norm_one

theorem counterexample_proved (p : ℝ) (_hp : 0 < p) :
    (∀ i : Fin 2, (witnessA i).PosDef ∧ (witnessB i).PosDef) ∧
    (∑ i, witnessA i) = 1 ∧ (∑ i, witnessB i) = 1 ∧
    leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2 = witnessL ∧
    rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p = 1 ∧
    witnessVector ≠ 0 ∧
    witnessL *ᵥ witnessVector = (witnessEigenvalue : ℂ) • witnessVector ∧
    1 < witnessEigenvalue ∧
    witnessEigenvalue ≤ operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) = 1 ∧
    operatorNorm (rightMatrix witnessA witnessB (1 / 2) (1 / 2) 2 p) <
      operatorNorm (leftMatrix witnessA witnessB (1 / 2) (1 / 2) 2) := by
  refine ⟨witness_inputs_posDef, witness_sum_A, witness_sum_B, witness_left_matrix,
    witness_right_matrix p, witness_vector_ne_zero, witness_eigenvector,
    witness_eigenvalue_gt_one, witness_left_norm_lower_bound, witness_right_norm p, ?_⟩
  rw [witness_right_norm]
  exact lt_of_lt_of_le witness_eigenvalue_gt_one witness_left_norm_lower_bound

theorem not_geometricMeanNormConjecture_proved : ¬ GeometricMeanNormConjecture := by
  intro h
  have hi := h 2 2 (by norm_num) (by norm_num) witnessA witnessB
    (fun i => (witness_inputs_posDef i).1) (fun i => (witness_inputs_posDef i).2)
    (1 / 2) (1 / 2) 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) operatorNorm (operatorNorm_isUnitaryInvariant_proved 2)
  rcases counterexample_proved 1 (by norm_num) with
    ⟨_, _, _, _, _, _, _, _, _, _, hstrict⟩
  exact (not_le_of_gt hstrict) hi

#assert_trust kernel operatorNorm_isUnitaryInvariant_proved
#assert_trust kernel geometricMean_eq_of_riccati
#assert_trust kernel mean_squared_of_scaled_riccati
#assert_trust kernel witness_left_matrix
#assert_trust kernel real_eigenvalue_le_operatorNorm
#assert_trust kernel witness_eigenvalue_gt_one
#assert_trust kernel counterexample_proved
#assert_trust kernel not_geometricMeanNormConjecture_proved

#print axioms operatorNorm_isUnitaryInvariant_proved
#print axioms geometricMean_eq_of_riccati
#print axioms mean_squared_of_scaled_riccati
#print axioms witness_left_matrix
#print axioms real_eigenvalue_le_operatorNorm
#print axioms witness_eigenvalue_gt_one
#print axioms counterexample_proved
#print axioms not_geometricMeanNormConjecture_proved

end NLA.MI21
