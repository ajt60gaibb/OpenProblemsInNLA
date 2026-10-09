import ProofProject.PhaseCoefficientPolynomial
import ProofProject.FiniteToeplitz

/-! Contractive Toeplitz interpolation data from the actual outer phase. -/

noncomputable section

open Polynomial

namespace ProofProject

/-- The actual finite moment polynomial has the exact projection-angle bound. -/
theorem phaseCoefficientPolynomial_toeplitz_bound {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 ≤ K)
    (m : ℕ) (hdeg : h.natDegree ≤ m) :
    HasFiniteToeplitzBound (phaseCoefficientPolynomial h m).coeff m
      (Real.sqrt (1 - K⁻¹ ^ 2)) := by
  have hvan : ∀ k, m ≤ k → phaseNegativeMoment (polynomialCirclePhase h) k = 0 :=
    fun k hk => polynomialCirclePhase_negativeMoment_eq_zero hh (hdeg.trans hk)
  apply (polynomialCirclePhase_toeplitz_bound hh hproj hK hvan).congr_prefix
  intro k hk
  simp only [reversedMomentCoefficients, phaseCoefficientPolynomial_coeff, if_pos hk]

/-- The coefficient congruence and contractive matrix are constructed together.
They are precisely the finite data needed by the subsequent Schur interpolation. -/
theorem exists_outerToeplitzData {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 < K)
    (m : ℕ) (hdeg : h.natDegree ≤ m) :
    ∃ p : Polynomial ℂ,
      (∀ j : ℕ, m ≤ j → p.coeff j = 0) ∧
      HasFiniteToeplitzBound p.coeff m 1 ∧
      X ^ m ∣ reflect m (h.map (starRingEnd ℂ)) -
        C (Real.sqrt (1 - K⁻¹ ^ 2) : ℂ) * h * p := by
  let ρ := Real.sqrt (1 - K⁻¹ ^ 2)
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hi0 : 0 ≤ K⁻¹ := inv_nonneg.mpr hKpos.le
  have hi1 : K⁻¹ < 1 := (inv_lt_one₀ hKpos).2 hK
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (by nlinarith)
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  let D := phaseCoefficientPolynomial h m
  let p := C ((ρ : ℂ)⁻¹) * D
  refine ⟨p, ?_, ?_, ?_⟩
  · intro j hj
    simp [p, D, coeff_C_mul, phaseCoefficientPolynomial_coeff, not_lt.mpr hj]
  · have hb := (phaseCoefficientPolynomial_toeplitz_bound hh hproj hK.le m hdeg).normalize hρ
    apply hb.congr_prefix
    intro j hj
    simp only [p, coeff_C_mul, D, ρ]
  · have hscale : C (ρ : ℂ) * h * p = h * D := by
      dsimp only [p]
      calc
        _ = (C (ρ : ℂ) * C ((ρ : ℂ)⁻¹)) * (h * D) := by ring
        _ = h * D := by
          rw [← map_mul, mul_inv_cancel₀ hρc, map_one, one_mul]
    change X ^ m ∣ reflect m (h.map (starRingEnd ℂ)) - C (ρ : ℂ) * h * p
    rw [hscale]
    exact phaseCoefficientPolynomial_divisibility h hh m hdeg

end ProofProject
