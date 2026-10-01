import ProofProject.CircleGramPolynomial

/-!
# Finite Hankel energy from a circle pairing estimate

The positive frequencies are `j`, and the strictly negative frequencies are
`-i-1`. The Hankel entry at `(i,j)` is therefore the moment against character
`i+j+1`, with no conjugation on the moment. Only finite sums and scalar
integration are used; no Taylor series or infinite Hardy space is assumed.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

variable {m n : ℕ}

def circleAnalyticPolynomial (a : Fin n → ℂ) (z : AddCircle (1 : ℝ)) : ℂ :=
  ∑ j, fourier (j.val : ℤ) z * a j

def circleStrictNegativePolynomial (b : Fin m → ℂ) (z : AddCircle (1 : ℝ)) : ℂ :=
  ∑ i, fourier (-((i.val : ℤ) + 1)) z * b i

/-- The Fourier coefficient at frequency `-k-1`. -/
def phaseNegativeMoment (g : AddCircle (1 : ℝ) → ℂ) (k : ℕ) : ℂ :=
  ∫ z, g z * fourier ((k : ℤ) + 1) z ∂AddCircle.haarAddCircle

lemma phaseNegativeMoment_eq_fourierCoeff (g : AddCircle (1 : ℝ) → ℂ) (k : ℕ) :
    phaseNegativeMoment g k = fourierCoeff g (-((k : ℤ) + 1)) := by
  simp only [phaseNegativeMoment, fourierCoeff, neg_neg, smul_eq_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => mul_comm _ _

def finiteHankelApply (g : AddCircle (1 : ℝ) → ℂ) (a : Fin n → ℂ) : Fin m → ℂ :=
  fun i => ∑ j, phaseNegativeMoment g (i.val + j.val) * a j

lemma continuous_circleAnalyticPolynomial (a : Fin n → ℂ) :
    Continuous (circleAnalyticPolynomial a) :=
  continuous_finsetSum _ fun j _ => (fourier (j.val : ℤ)).continuous.mul continuous_const

lemma continuous_circleStrictNegativePolynomial (b : Fin m → ℂ) :
    Continuous (circleStrictNegativePolynomial b) :=
  continuous_finsetSum _ fun i _ =>
    (fourier (-((i.val : ℤ) + 1))).continuous.mul continuous_const

lemma circleAnalyticPolynomial_eq_eval (a : Fin n → ℂ) (z : AddCircle (1 : ℝ)) :
    circleAnalyticPolynomial a z =
      (∑ j : Fin n, Polynomial.monomial j.val (a j)).eval (fourier 1 z) := by
  simp only [circleAnalyticPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, circleGram_fourier_nat]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma circleStrictNegativePolynomial_eq_conj (b : Fin m → ℂ)
    (z : AddCircle (1 : ℝ)) :
    circleStrictNegativePolynomial b z = fourier (-1) z *
      starRingEnd ℂ (circleAnalyticPolynomial (fun i => starRingEnd ℂ (b i)) z) := by
  simp only [circleStrictNegativePolynomial, circleAnalyticPolynomial,
    map_sum, map_mul, starRingEnd_self_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hf : -((i.val : ℤ) + 1) = -1 + -(i.val : ℤ) := by ring
  rw [hf, fourier_add]
  simp only [fourier_neg]
  ring

lemma circleAnalyticPolynomial_integral (a : Fin n → ℂ) :
    (∫ z : AddCircle (1 : ℝ), ‖circleAnalyticPolynomial a z‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ j, ‖a j‖ ^ 2 := by
  simpa only [circleAnalyticPolynomial, smul_eq_mul] using
    finiteCircleParseval_indexed (fun j : Fin n => (j.val : ℤ))
      (by intro i j hij; dsimp only at hij; apply Fin.ext; omega) a

lemma circleStrictNegativePolynomial_integral (b : Fin m → ℂ) :
    (∫ z : AddCircle (1 : ℝ), ‖circleStrictNegativePolynomial b z‖ ^ 2
      ∂AddCircle.haarAddCircle) = ∑ i, ‖b i‖ ^ 2 := by
  simpa only [circleStrictNegativePolynomial, smul_eq_mul] using
    finiteCircleParseval_indexed (fun i : Fin m => -((i.val : ℤ) + 1))
      (by intro i j hij; dsimp only at hij; apply Fin.ext; omega) b

set_option backward.isDefEq.respectTransparency.types false in
private lemma integrable_phase_character {g : AddCircle (1 : ℝ) → ℂ}
    (hg : Continuous g) (k : ℤ) :
    Integrable (fun z => g z * fourier k z) AddCircle.haarAddCircle := by
  simpa only [MeasureTheory.integrableOn_univ, Pi.mul_def] using!
    (hg.mul (fourier k).continuous).continuousOn.integrableOn_compact
      (μ := AddCircle.haarAddCircle) isCompact_univ

/-- The pairing is linear in the analytic input, conjugate-linear in the
negative-frequency test, and has Hankel entries with no extra conjugation. -/
theorem finiteHankel_pairing {g : AddCircle (1 : ℝ) → ℂ} (hg : Continuous g)
    (a : Fin n → ℂ) (b : Fin m → ℂ) :
    (∫ z, g z * circleAnalyticPolynomial a z *
      starRingEnd ℂ (circleStrictNegativePolynomial b z) ∂AddCircle.haarAddCircle) =
      ∑ i, starRingEnd ℂ (b i) * finiteHankelApply g a i := by
  have hpoint (z : AddCircle (1 : ℝ)) :
      g z * circleAnalyticPolynomial a z * starRingEnd ℂ (circleStrictNegativePolynomial b z) =
        ∑ i : Fin m, ∑ j : Fin n,
          (g z * fourier (((i.val + j.val : ℕ) : ℤ) + 1) z) *
            (starRingEnd ℂ (b i) * a j) := by
    simp only [circleAnalyticPolynomial, circleStrictNegativePolynomial, map_sum,
      map_mul, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have hc : starRingEnd ℂ (fourier (-((i.val : ℤ) + 1)) z) =
        fourier ((i.val : ℤ) + 1) z := by rw [fourier_neg]; simp
    have hf : ((i.val + j.val : ℕ) : ℤ) + 1 = (j.val : ℤ) + ((i.val : ℤ) + 1) := by
      push_cast
      ring
    rw [hc, hf]
    simp only [fourier_add]
    ring
  calc
    _ = ∫ z, ∑ i : Fin m, ∑ j : Fin n,
        (g z * fourier (((i.val + j.val : ℕ) : ℤ) + 1) z) *
          (starRingEnd ℂ (b i) * a j) ∂AddCircle.haarAddCircle :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∑ i : Fin m, ∑ j : Fin n,
        ∫ z, (g z * fourier (((i.val + j.val : ℕ) : ℤ) + 1) z) *
          (starRingEnd ℂ (b i) * a j) ∂AddCircle.haarAddCircle := by
      rw [integral_finsetSum Finset.univ (fun i _ => integrable_finsetSum Finset.univ
        fun j _ => (integrable_phase_character hg _).mul_const _)]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum Finset.univ
        (fun j _ => (integrable_phase_character hg _).mul_const _)
    _ = _ := by
      simp only [integral_mul_const, phaseNegativeMoment, finiteHankelApply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Testing on the Hankel output turns the circle pairing estimate into the
exact finite Euclidean energy bound. Empty input and output families are allowed. -/
theorem finiteHankel_energy_le {g : AddCircle (1 : ℝ) → ℂ} (hg : Continuous g)
    (ρ : ℝ)
    (hpair : ∀ (a : Fin n → ℂ) (b : Fin m → ℂ),
      ‖∫ z, g z * circleAnalyticPolynomial a z *
        starRingEnd ℂ (circleStrictNegativePolynomial b z) ∂AddCircle.haarAddCircle‖ ^ 2 ≤
        ρ ^ 2 * (∫ z : AddCircle (1 : ℝ), ‖circleAnalyticPolynomial a z‖ ^ 2
          ∂AddCircle.haarAddCircle) *
        (∫ z : AddCircle (1 : ℝ), ‖circleStrictNegativePolynomial b z‖ ^ 2
          ∂AddCircle.haarAddCircle))
    (a : Fin n → ℂ) :
    (∑ i : Fin m, ‖finiteHankelApply g a i‖ ^ 2) ≤ ρ ^ 2 * ∑ j, ‖a j‖ ^ 2 := by
  let y : Fin m → ℂ := finiteHankelApply g a
  let E : ℝ := ∑ i, ‖y i‖ ^ 2
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have htest := hpair a y
  have heq : (∫ z, g z * circleAnalyticPolynomial a z *
      starRingEnd ℂ (circleStrictNegativePolynomial y z) ∂AddCircle.haarAddCircle) = (E : ℂ) := by
    rw [finiteHankel_pairing hg]
    change (∑ i, starRingEnd ℂ (y i) * y i) = ((∑ i, ‖y i‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE0,
    circleAnalyticPolynomial_integral, circleStrictNegativePolynomial_integral] at htest
  change E ^ 2 ≤ (ρ ^ 2 * ∑ j, ‖a j‖ ^ 2) * E at htest
  change E ≤ _
  by_cases hE : E = 0
  · rw [hE]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne hE0 (Ne.symm hE))).mp
      (by simpa only [pow_two, mul_comm E] using htest)

end ProofProject
