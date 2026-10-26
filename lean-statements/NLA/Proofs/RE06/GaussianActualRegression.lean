import NLA.Proofs.RE06.GaussianRegressionMoment

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem rangeDimension_le_rows {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    rangeDimension Y ≤ n := by
  simpa [rangeDimension] using
    Submodule.finrank_le (LinearMap.range (Matrix.toEuclideanLin Y))

theorem orthonormal_gaussian_gram_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n d ell : ℕ} (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (hd : d ≤ n) (hdell : d ≤ ell)
    (X : Ω → (Fin n × Fin ell → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1)) μ) :
    ∀ᵐ ω ∂μ, ((((Matrix.of (fun i j => X ω (i,j))).transpose*Q).transpose)*
      ((Matrix.of (fun i j => X ω (i,j))).transpose*Q)).det ≠ 0 := by
  obtain ⟨O,hOg,hOc,hOE⟩ := exists_orthogonal_completion Q hQ hd
  have hRot := hasLaw_fixed_gaussian_rotation μ O hOc ell X hX
  have hHead := (gaussian_head_entries_hasLaw n d ell hd).fun_comp hRot
  have hdet := GaussianMoment.hasLaw_gram_det_ne_zero_ae μ d ell hdell _ hHead
  filter_upwards [hdet] with ω hω
  have he := congrArg Matrix.transpose (regression_head_coordinates O hd Q hOE (X ω))
  simp only [Matrix.transpose_transpose] at he
  change ((Matrix.of (fun i j => gaussianHeadEntries n d ell hd (rotateEntries O ell (X ω)) (i,j)))*
    (Matrix.of (fun i j => gaussianHeadEntries n d ell hd (rotateEntries O ell (X ω)) (i,j))).transpose).det≠0 at hω
  rw [he, Matrix.transpose_transpose] at hω
  exact hω

/-- The actual fixed-width SVD repair regression excess has the exact Gaussian
moment for every fixed Y, including rank-zero and deficient Y. -/
theorem actual_regression_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {n k c ell : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ) (hDell : rangeDimension Y+1<ell)
    (X : Ω → (Fin n × Fin ell → ℝ))
    (hX : HasLaw X (Measure.pi (fun _ : Fin n × Fin ell => gaussianReal 0 1)) μ) :
    Integrable (fun ω => actualRegressionEnergy Y C
      (Matrix.of (fun i j => X ω (i,j))).transpose) μ ∧
      (∫ ω, actualRegressionEnergy Y C
        (Matrix.of (fun i j => X ω (i,j))).transpose ∂μ) =
        ((rangeDimension Y:ℝ)/((ell:ℝ)-(rangeDimension Y:ℝ)-1))*
          squaredFrobenius (actualRangeResidual Y C) 0 := by
  let Q := rangeBasisMatrix Y
  have hQ : Q.transpose*Q=1 := rangeBasisMatrix_gram Y
  have hd : rangeDimension Y≤n := rangeDimension_le_rows Y
  have hrange : Set.range Q.mulVec=Set.range Y.mulVec := rangeBasisMatrix_range Y
  have hR : Q.transpose*rangeResidual Q C=0 := rangeResidual_orthogonal Q hQ C
  have hm := gaussian_regression_energy_moment μ Q hQ hd (rangeResidual Q C) hR hDell X hX
  have hS := orthonormal_gaussian_gram_ae μ Q hQ hd (by omega) X hX
  have hEq : (fun ω => actualRegressionEnergy Y C
      (Matrix.of (fun i j => X ω (i,j))).transpose) =ᵐ[μ]
      (fun ω => squaredFrobenius
        (pseudoInverse ((Matrix.of (fun i j => X ω (i,j))).transpose*Q)*
          ((Matrix.of (fun i j => X ω (i,j))).transpose*rangeResidual Q C)) 0) := by
    filter_upwards [hS] with ω hω
    exact actualRegressionEnergy_basis Y Q hQ C _ hrange hω
  refine ⟨hm.1.congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq, hm.2, actualRangeResidual_basis Y Q hQ hrange]

#assert_trust kernel rangeDimension_le_rows
#assert_trust kernel orthonormal_gaussian_gram_ae
#assert_trust kernel actual_regression_moment
#print axioms actual_regression_moment
end NLA.Proofs.RE06.Repair
