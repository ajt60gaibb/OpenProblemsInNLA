import ProofProject.RationalCircleAngle
import ProofProject.FiniteHankelForm

/-! The exact finite Hankel bound obtained from the polynomial weighted projection. -/

noncomputable section

open MeasureTheory

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The negative Fourier moments of the outer phase give a finite Hankel
contraction with the exact projection-angle constant. This is a Euclidean
sum-of-squares bound, allowing arbitrary finite input and output sizes. -/
theorem polynomialCirclePhase_hankel_energy_le {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 ≤ K)
    {m n : ℕ} (a : Fin n → ℂ) :
    (∑ i : Fin m, ‖finiteHankelApply (polynomialCirclePhase h) a i‖ ^ 2) ≤
      (1 - K⁻¹ ^ 2) * ∑ j, ‖a j‖ ^ 2 := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hinv0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hinv1 : K⁻¹ ≤ 1 := (inv_le_one₀ hKpos).2 hK
  have hρ : (Real.sqrt (1 - K⁻¹ ^ 2)) ^ 2 = 1 - K⁻¹ ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  rw [← hρ]
  apply finiteHankel_energy_le (continuous_polynomialCirclePhase h hh)
  intro x y
  let A : Polynomial ℂ := ∑ j : Fin n, Polynomial.monomial j.val (x j)
  let B : Polynomial ℂ := ∑ i : Fin m, Polynomial.monomial i.val (starRingEnd ℂ (y i))
  have hA (z : AddCircle (1 : ℝ)) : circleAnalyticPolynomial x z = A.eval (fourier 1 z) :=
    circleAnalyticPolynomial_eq_eval x z
  have hB (z : AddCircle (1 : ℝ)) : circleStrictNegativePolynomial y z =
      fourier (-1) z * starRingEnd ℂ (B.eval (fourier 1 z)) := by
    rw [circleStrictNegativePolynomial_eq_conj, circleAnalyticPolynomial_eq_eval]
  have hnormB (z : AddCircle (1 : ℝ)) :
      ‖circleStrictNegativePolynomial y z‖ = ‖B.eval (fourier 1 z)‖ := by
    rw [hB, norm_mul, finiteCircle_fourier_norm, one_mul, starRingEnd_apply, norm_star]
  have hpoint (z : AddCircle (1 : ℝ)) :
      polynomialCirclePhase h z * circleAnalyticPolynomial x z *
          starRingEnd ℂ (circleStrictNegativePolynomial y z) =
        polynomialCirclePhase h z * A.eval (fourier 1 z) * fourier 1 z * B.eval (fourier 1 z) := by
    rw [hA, hB]
    simp only [map_mul, fourier_neg, starRingEnd_self_apply]
    ring
  simp_rw [hpoint, hA, hnormB, hρ]
  exact polynomialCirclePhase_angle_sq hh hproj hK A B

/-- The same bound in the genuine Euclidean norms, rather than the supremum
norm on a function space or a default matrix norm. -/
theorem polynomialCirclePhase_hankel_norm_le {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 ≤ K)
    {m n : ℕ} (a : EuclideanSpace ℂ (Fin n)) :
    ‖(WithLp.toLp 2 (finiteHankelApply (m := m) (polynomialCirclePhase h)
      (fun j => a j)) : EuclideanSpace ℂ (Fin m))‖ ≤
      Real.sqrt (1 - K⁻¹ ^ 2) * ‖a‖ := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hinv0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hinv1 : K⁻¹ ≤ 1 := (inv_le_one₀ hKpos).2 hK
  have hρ : (Real.sqrt (1 - K⁻¹ ^ 2)) ^ 2 = 1 - K⁻¹ ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, hρ, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  exact polynomialCirclePhase_hankel_energy_le hh hproj hK (fun j => a j)

end ProofProject
