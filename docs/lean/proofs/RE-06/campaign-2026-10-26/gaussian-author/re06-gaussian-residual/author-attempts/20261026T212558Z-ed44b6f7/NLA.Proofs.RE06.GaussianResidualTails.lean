import NLA.Proofs.RE06.GaussianResidualTransport

/-! Spectral-tail bounds for actual fixed residual matrix sketches, including
zero residuals and zero singular-value tails. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- The head is the first `r` singular values, in the actual SVD order. -/
def residualSpectralHead (n r : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < r)

/-- Squared singular-value energy after removing the first `r` values. -/
def residualTailEnergy {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ (residualSpectralHead n r)ᶜ, (residualSingularValue B i) ^ 2

theorem residualSpectralHead_card (n r : ℕ) (hr : r ≤ n) :
    (residualSpectralHead n r).card = r := by
  rw [residualSpectralHead, Fin.card_filter_val_lt, Nat.min_eq_right hr]

theorem residual_singular_energy {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) :
    (∑ i, (residualSingularValue B i) ^ 2) = squaredFrobenius B 0 := by
  symm
  rw [residual_svd_reconstruction B, Matrix.mul_assoc,
    squaredFrobenius_left_isometry _ (Pseudo.svd_U_gram B),
    squaredFrobenius_right_isometry _ (Pseudo.svd_V_gram B)]
  simp [squaredFrobenius, Matrix.diagonal_apply]

theorem residual_weight_head {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r < n) (i : Fin n) (hi : i ∈ residualSpectralHead n r) :
    (residualSingularValue B ⟨r, hr⟩) ^ 2 ≤ (residualSingularValue B i) ^ 2 := by
  have hival : i.val < r := (Finset.mem_filter.mp hi).2
  have hσ := residualSingularValue_antitone B (show i ≤ ⟨r, hr⟩ by exact hival.le)
  have hp := mul_nonneg (sub_nonneg.mpr hσ)
    (add_nonneg (residualSingularValue_nonneg B i) (residualSingularValue_nonneg B ⟨r, hr⟩))
  nlinarith

theorem residual_weight_tail {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r < n) (i : Fin n) (hi : i ∉ residualSpectralHead n r) :
    (residualSingularValue B i) ^ 2 ≤ (residualSingularValue B ⟨r, hr⟩) ^ 2 := by
  have hival : r ≤ i.val := by
    simp only [residualSpectralHead, Finset.mem_filter, Finset.mem_univ, true_and,
      not_lt] at hi
    exact hi
  have hσ := residualSingularValue_antitone B (show (⟨r, hr⟩ : Fin n) ≤ i by exact hival)
  have hp := mul_nonneg (sub_nonneg.mpr hσ)
    (add_nonneg (residualSingularValue_nonneg B i) (residualSingularValue_nonneg B ⟨r, hr⟩))
  nlinarith

/-- The manuscript's trimmed lower tail for the actual unscaled block. -/
theorem residualGaussian_lower_tail {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q offset r : ℕ) (hr : r < n) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω | squaredFrobenius (B * gaussianBlock n q offset ω) 0 <
      (q : ℝ) * (1 - η) * residualTailEnergy B r} ≤
      Real.exp (-(q : ℝ) * (r : ℝ) * η / 4) := by
  have h := gaussianQuadratic_trimmed_lower_tail_of_hasLaw q
    (residualGaussianCoordinates B q offset) (residualGaussianCoordinates_hasLaw B q offset)
    (fun i => (residualSingularValue B i) ^ 2) (fun i => sq_nonneg _)
    (residualSpectralHead n r) ((residualSingularValue B ⟨r, hr⟩) ^ 2) (sq_nonneg _)
    (residual_weight_head B r hr) (residual_weight_tail B r hr) η hη0 hη1
  simpa only [← residualGaussian_energy, residualSpectralHead_card n r hr.le,
    residualTailEnergy] using h

/-- The one fixed-residual upper tail for the actual unscaled block. -/
theorem residualGaussian_upper_tail {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ)
    (q offset : ℕ) (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    GaussianLaw.real {ω | (q : ℝ) * (1 + η) * squaredFrobenius B 0 <
      squaredFrobenius (B * gaussianBlock n q offset ω) 0} ≤
      Real.exp (-(q : ℝ) * η ^ 2 / 8) := by
  have h := gaussianQuadratic_upper_tail_of_hasLaw q
    (residualGaussianCoordinates B q offset) (residualGaussianCoordinates_hasLaw B q offset)
    (fun i => (residualSingularValue B i) ^ 2) (fun i => sq_nonneg _) η hη0 hη1
  simpa only [← residualGaussian_energy, residual_singular_energy] using h

#assert_trust kernel residualSpectralHead_card
#assert_trust kernel residual_singular_energy
#assert_trust kernel residual_weight_head
#assert_trust kernel residual_weight_tail
#assert_trust kernel residualGaussian_lower_tail
#assert_trust kernel residualGaussian_upper_tail
#print axioms residualSpectralHead_card
#print axioms residual_singular_energy
#print axioms residual_weight_head
#print axioms residual_weight_tail
#print axioms residualGaussian_lower_tail
#print axioms residualGaussian_upper_tail
end NLA.Proofs.RE06
