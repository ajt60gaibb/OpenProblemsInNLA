import ProofProject.PolynomialPhaseMoments

/-! The finite polynomial determined by the negative moments of an outer phase. -/

noncomputable section

open MeasureTheory Polynomial

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def phaseCoefficientPolynomial (h : Polynomial ℂ) (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range m,
    monomial j (phaseNegativeMoment (polynomialCirclePhase h) (m - 1 - j))

lemma phaseCoefficientPolynomial_coeff (h : Polynomial ℂ) (m j : ℕ) :
    (phaseCoefficientPolynomial h m).coeff j =
      if j < m then phaseNegativeMoment (polynomialCirclePhase h) (m - 1 - j) else 0 := by
  simp [phaseCoefficientPolynomial, coeff_monomial]

lemma phaseCoefficientPolynomial_natDegree_lt (h : Polynomial ℂ) {m : ℕ} (hm : 0 < m) :
    (phaseCoefficientPolynomial h m).natDegree < m := by
  by_cases hp : phaseCoefficientPolynomial h m = 0
  · simpa [hp] using hm
  apply (natDegree_lt_iff_degree_lt hp).mpr
  apply (degree_lt_iff_coeff_zero _ m).mpr
  intro j hj
  simp [phaseCoefficientPolynomial_coeff, not_lt.mpr hj]

/-- Multiplication by h turns the phase moments into reflected coefficients.
The shift m-j is positive, so every intermediate moment has a natural index. -/
lemma phaseMoment_convolution (h : Polynomial ℂ)
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) {m j : ℕ}
    (hdeg : h.natDegree ≤ m) (hj : j < m) :
    (∑ i ∈ Finset.range (m + 1), h.coeff i *
      phaseNegativeMoment (polynomialCirclePhase h) (m - j + i - 1)) =
        starRingEnd ℂ (h.coeff (m - j)) := by
  have hg := continuous_polynomialCirclePhase h hh
  have hpoint (z : AddCircle (1 : ℝ)) :
      h.eval (fourier 1 z) * polynomialCirclePhase h z * fourier ((m - j : ℕ) : ℤ) z =
        ∑ i ∈ Finset.range (m + 1), h.coeff i *
          (polynomialCirclePhase h z * fourier (((m - j + i - 1 : ℕ) : ℤ) + 1) z) := by
    rw [eval_eq_sum_range' (by omega : h.natDegree < m + 1)]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (((m - j + i - 1 : ℕ) : ℤ) + 1) = (i : ℤ) + ((m - j : ℕ) : ℤ) := by omega
    rw [he, fourier_add]
    simp only [circleGram_fourier_nat]
    ring
  have hint (i : ℕ) : Integrable (fun z : AddCircle (1 : ℝ) => h.coeff i *
      (polynomialCirclePhase h z * fourier (((m - j + i - 1 : ℕ) : ℤ) + 1) z))
      AddCircle.haarAddCircle := by
    simpa only [MeasureTheory.integrableOn_univ, Pi.mul_def] using
      (continuous_const.mul (hg.mul (fourier _).continuous)).continuousOn.integrableOn_compact
        (μ := AddCircle.haarAddCircle) isCompact_univ
  calc
    _ = ∑ i ∈ Finset.range (m + 1),
        ∫ z : AddCircle (1 : ℝ), h.coeff i *
          (polynomialCirclePhase h z * fourier (((m - j + i - 1 : ℕ) : ℤ) + 1) z)
            ∂AddCircle.haarAddCircle := by
      simp only [integral_const_mul, phaseNegativeMoment]
    _ = ∫ z : AddCircle (1 : ℝ), ∑ i ∈ Finset.range (m + 1), h.coeff i *
          (polynomialCirclePhase h z * fourier (((m - j + i - 1 : ℕ) : ℤ) + 1) z)
            ∂AddCircle.haarAddCircle :=
      (integral_finsetSum _ (fun i _ => hint i)).symm
    _ = ∫ z : AddCircle (1 : ℝ), h.eval (fourier 1 z) * polynomialCirclePhase h z *
        fourier ((m - j : ℕ) : ℤ) z ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (hpoint z).symm
    _ = _ := polynomialCirclePhase_mul_moment h hh (m - j)

/-- The unscaled moment polynomial is the finite reciprocal data of the
padded reflected polynomial. This identity does not need a projection bound. -/
theorem phaseCoefficientPolynomial_divisibility (h : Polynomial ℂ)
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) (m : ℕ) (hdeg : h.natDegree ≤ m) :
    X ^ m ∣ reflect m (h.map (starRingEnd ℂ)) - h * phaseCoefficientPolynomial h m := by
  apply X_pow_dvd_iff.mpr
  intro j hj
  rw [coeff_sub, sub_eq_zero, coeff_reflect, coeff_map,
    revAt_le (by omega : j ≤ m), coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  symm
  calc
    _ = ∑ i ∈ Finset.range (j + 1), h.coeff i *
        phaseNegativeMoment (polynomialCirclePhase h) (m - j + i - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ j := by have := Finset.mem_range.mp hi; omega
      rw [phaseCoefficientPolynomial_coeff, if_pos (by omega : j - i < m)]
      congr 2
      omega
    _ = ∑ i ∈ Finset.range (m + 1), h.coeff i *
        phaseNegativeMoment (polynomialCirclePhase h) (m - j + i - 1) := by
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro i hi hnot
      have hji : j < i := by simp only [Finset.mem_range] at hnot; omega
      have hzero := polynomialCirclePhase_negativeMoment_eq_zero hh
        (show h.natDegree ≤ m - j + i - 1 by omega)
      rw [hzero, mul_zero]
    _ = _ := phaseMoment_convolution h hh hdeg hj

end ProofProject
