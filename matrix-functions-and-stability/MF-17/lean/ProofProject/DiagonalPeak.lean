import ProofProject.DiagonalOperators
import ProofProject.ScalarEigenvalues

/-! The finite diagonal inverse exponential approximates the prescribed signs. -/

noncomputable section

namespace ProofProject

/-- A scaled, shifted eigenvalue of the stable generator. -/
def peakEigenvalue (ω y : ℝ) : ℂ := (ω : ℂ)⁻¹ * scalarLambda y - 1

lemma peakEigenvalue_factor (ω y : ℝ) (hω : ω ≠ 0) :
    peakEigenvalue ω y = (ω : ℂ)⁻¹ * (scalarLambda y - (ω : ℂ)) := by
  unfold peakEigenvalue
  rw [mul_sub, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hω)]

lemma peakEigenvalue_ne_zero (ω y : ℝ) (hω : 0 < ω) : peakEigenvalue ω y ≠ 0 := by
  rw [peakEigenvalue_factor ω y hω.ne']
  exact mul_ne_zero (inv_ne_zero (Complex.ofReal_ne_zero.mpr hω.ne'))
    (scalarLambda_sub_ne_zero y ω hω.le)

lemma peakEigenvalue_inverse_time (ω y : ℝ) (hω : 0 < ω) :
    ((Real.pi / ω : ℝ) : ℂ) * (peakEigenvalue ω y)⁻¹ =
      (Real.pi : ℂ) * (scalarLambda y - (ω : ℂ))⁻¹ := by
  rw [peakEigenvalue_factor ω y hω.ne', mul_inv_rev, inv_inv, Complex.ofReal_div]
  field_simp [Complex.ofReal_ne_zero.mpr hω.ne', scalarLambda_sub_ne_zero y ω hω.le]

universe u

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [FiniteDimensional ℂ H] {N : ℕ}

/-- The finite generator in the source construction. -/
def diagonalPeakGenerator (b : Module.Basis (Fin N) ℂ H) (ω : ℝ) (y : Fin N → ℕ) :
    H →L[ℂ] H := basisDiagonal b (fun i => peakEigenvalue ω (y i))

/-- Its explicit inverse, prior to identifying it with the strong generator inverse. -/
def diagonalPeakInverse (b : Module.Basis (Fin N) ℂ H) (ω : ℝ) (y : Fin N → ℕ) :
    H →L[ℂ] H := basisDiagonal b (fun i => (peakEigenvalue ω (y i))⁻¹)

lemma diagonalPeak_mul_inverse (b : Module.Basis (Fin N) ℂ H) {ω : ℝ}
    (hω : 0 < ω) (y : Fin N → ℕ) :
    diagonalPeakGenerator b ω y * diagonalPeakInverse b ω y = 1 := by
  rw [diagonalPeakGenerator, diagonalPeakInverse, ← basisDiagonal_mul, ← basisDiagonal_one b]
  congr 1
  funext i
  exact mul_inv_cancel₀ (peakEigenvalue_ne_zero ω (y i) hω)

lemma diagonalPeak_inverse_mul (b : Module.Basis (Fin N) ℂ H) {ω : ℝ}
    (hω : 0 < ω) (y : Fin N → ℕ) :
    diagonalPeakInverse b ω y * diagonalPeakGenerator b ω y = 1 := by
  rw [diagonalPeakGenerator, diagonalPeakInverse, ← basisDiagonal_mul, ← basisDiagonal_one b]
  congr 1
  funext i
  exact inv_mul_cancel₀ (peakEigenvalue_ne_zero ω (y i) hω)

lemma diagonalPeak_evolution (b : Module.Basis (Fin N) ℂ H) {ω : ℝ}
    (hω : 0 < ω) (y : Fin N → ℕ) :
    inverseEvolution (diagonalPeakInverse b ω y) (Real.pi / ω) =
      basisDiagonal b (fun i => Complex.exp
        ((Real.pi : ℂ) * (scalarLambda (y i) - (ω : ℂ))⁻¹)) := by
  rw [inverseEvolution, diagonalPeakInverse, ← basisDiagonal_smul, basisDiagonal_exp]
  congr 1
  funext i
  congr 1
  exact peakEigenvalue_inverse_time ω (y i) hω

/-- The operator approximation retains the explicit coordinate-projection factor. -/
theorem diagonalPeak_sign_error (b : Module.Basis (Fin N) ℂ H) {ω K : ℝ}
    (hω : 0 < ω) (hK : 0 ≤ K) (y : Fin N → ℕ)
    (hcoord : ∀ i, ‖basisCoordinate b i‖ ≤ K) :
    ‖inverseEvolution (diagonalPeakInverse b ω y) (Real.pi / ω) -
      (Real.exp (-Real.pi) : ℂ) • basisDiagonal b (fun i => (-1 : ℂ) ^ y i)‖ ≤
      K * (Real.pi * ω) * ∑ i, (1 + (y i : ℝ) ^ 2) := by
  rw [diagonalPeak_evolution b hω y, ← basisDiagonal_smul]
  calc
    _ ≤ K * ∑ i, ‖Complex.exp ((Real.pi : ℂ) * (scalarLambda (y i) - (ω : ℂ))⁻¹) -
        (Real.exp (-Real.pi) : ℂ) * (-1 : ℂ) ^ y i‖ :=
      norm_basisDiagonal_sub_le b _ _ hcoord
    _ ≤ K * ∑ i, (Real.pi * ω) * (1 + (y i : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hK
      exact Finset.sum_le_sum fun i _ => scalarLambda_shift_exp_pi_error (y i) ω hω.le
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- An approximate sign change supplies the corresponding lower norm estimate. -/
theorem diagonalPeak_norm_lower (b : Module.Basis (Fin N) ℂ H) {ω K : ℝ}
    (hω : 0 < ω) (hK : 0 ≤ K) (y : Fin N → ℕ)
    (hcoord : ∀ i, ‖basisCoordinate b i‖ ≤ K) :
    Real.exp (-Real.pi) * ‖basisDiagonal b (fun i => (-1 : ℂ) ^ y i)‖ -
        K * (Real.pi * ω) * ∑ i, (1 + (y i : ℝ) ^ 2) ≤
      ‖inverseEvolution (diagonalPeakInverse b ω y) (Real.pi / ω)‖ := by
  have h := norm_sub_norm_le
    ((Real.exp (-Real.pi) : ℂ) • basisDiagonal b (fun i => (-1 : ℂ) ^ y i))
    (inverseEvolution (diagonalPeakInverse b ω y) (Real.pi / ω))
  rw [norm_sub_rev] at h
  have he := diagonalPeak_sign_error b hω hK y hcoord
  simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
  linarith

end ProofProject
