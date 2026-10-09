import ProofProject.SourcePolynomialHilbert
import ProofProject.FiniteMomentCoefficients

/-!
# Polynomial representatives and the source Hilbert inner products

The two raw representatives `ψ p` and `conj(ψ) p` belong to angular L². Their
finite-block orthogonality is the conjugate of the proved analytic-square
moment identity. The normalized Hilbert inner product retains its exact mass
factor, with the first argument conjugated as in Mathlib.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

lemma continuous_sourcePolynomial {n : ℕ} (a : Fin n → ℂ) :
    Continuous (sourcePolynomial a) := by
  unfold sourcePolynomial sourceCircle
  fun_prop

lemma measurable_sourcePolynomial {n : ℕ} (a : Fin n → ℂ) :
    Measurable (sourcePolynomial a) := (continuous_sourcePolynomial a).measurable

lemma measurable_sourceWeightFactor_polynomial (α : ℝ) {n : ℕ} (a : Fin n → ℂ) :
    Measurable (fun θ => sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) :=
  ((measurable_sourceWeightFactor α).comp measurable_sourceCircle).mul
    (measurable_sourcePolynomial a)

lemma measurable_sourceConjWeightFactor_polynomial (α : ℝ) {n : ℕ} (a : Fin n → ℂ) :
    Measurable (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
      sourcePolynomial a θ) := by
  exact (Complex.continuous_conj.measurable.comp
    ((measurable_sourceWeightFactor α).comp measurable_sourceCircle)).mul
    (measurable_sourcePolynomial a)

/-- Every finite weighted polynomial is an actual square-integrable function. -/
theorem sourceWeightFactor_polynomial_memLp {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    MemLp (fun θ => sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ)
      2 (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  have heq : (fun θ => sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) =
      (fun θ => ∑ i, a i * sourceWeightedMonomial α i.val θ) := by
    funext θ
    simp only [sourcePolynomial, sourceWeightedMonomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [heq]
  exact memLp_finsetSum _ fun i _ =>
    (sourceWeightedMonomial_memLp hα0 hα1 i.val).const_mul (a i)

/-- Conjugating the weight preserves the pointwise norm and hence L² membership. -/
theorem sourceConjWeightFactor_polynomial_memLp {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    MemLp (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
      sourcePolynomial a θ) 2 (volume.restrict (Set.Icc (-Real.pi) Real.pi)) := by
  apply (sourceWeightFactor_polynomial_memLp hα0 hα1 a).congr_norm
    (measurable_sourceConjWeightFactor_polynomial α a).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun θ => by simp only [norm_mul, Complex.norm_conj]

/-- Integrability of the raw squared polynomial energy. -/
theorem sourceWeightFactor_polynomial_norm_sq_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    IntegrableOn (fun θ => ‖sourceWeightFactor α (sourceCircle θ) *
      sourcePolynomial a θ‖ ^ 2) (Set.Icc (-Real.pi) Real.pi) :=
  (sourceWeightFactor_polynomial_memLp hα0 hα1 a).integrable_norm_pow (by norm_num)

/-- Integrability of the conjugated-weight squared polynomial energy. -/
theorem sourceConjWeightFactor_polynomial_norm_sq_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    IntegrableOn (fun θ => ‖starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
      sourcePolynomial a θ‖ ^ 2) (Set.Icc (-Real.pi) Real.pi) :=
  (sourceConjWeightFactor_polynomial_memLp hα0 hα1 a).integrable_norm_pow (by norm_num)

theorem sourceWeightFactor_polynomial_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    IntegrableOn (fun θ => sourceWeightFactor α (sourceCircle θ) *
      sourcePolynomial a θ) (Set.Icc (-Real.pi) Real.pi) :=
  MemLp.integrable (by norm_num) (sourceWeightFactor_polynomial_memLp hα0 hα1 a)

theorem sourceConjWeightFactor_polynomial_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n : ℕ} (a : Fin n → ℂ) :
    IntegrableOn (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
      sourcePolynomial a θ) (Set.Icc (-Real.pi) Real.pi) :=
  MemLp.integrable (by norm_num) (sourceConjWeightFactor_polynomial_memLp hα0 hα1 a)

/-- The raw Hilbert cross integrand is integrable without support restrictions. -/
theorem sourceWeightFactor_polynomial_inner_integrable {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n m : ℕ}
    (a : Fin n → ℂ) (b : Fin m → ℂ) :
    IntegrableOn (fun θ =>
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) *
        (starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ))
      (Set.Icc (-Real.pi) Real.pi) :=
  (sourceWeightFactor_polynomial_memLp hα0 hα1 a).star.integrable_mul
    (sourceConjWeightFactor_polynomial_memLp hα0 hα1 b)

/-- The complex Hilbert cross integral is explicitly the conjugate of the
analytic-square integral, so disjoint upper/lower blocks are orthogonal. -/
theorem sourceWeightFactor_polynomial_inner_integral_eq_zero {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {n m cut : ℕ}
    (a : Fin n → ℂ) (b : Fin m → ℂ)
    (ha : ∀ i, a i ≠ 0 → cut ≤ i.val)
    (hb : ∀ j, b j ≠ 0 → j.val < cut) :
    (∫ θ in Set.Icc (-Real.pi) Real.pi,
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) *
        (starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ)) = 0 := by
  have heq : (fun θ =>
      starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ) *
        (starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) * sourcePolynomial b θ)) =
      (fun θ => starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ) ^ 2 *
        sourcePolynomial a θ * starRingEnd ℂ (sourcePolynomial b θ))) := by
    funext θ
    simp only [map_mul, map_pow, starRingEnd_self_apply]
    ring
  rw [heq, integral_conj,
    sourceWeightFactor_sq_polynomial_orthogonality hα0 hα1 a b ha hb, map_zero]

/-- The exact unit-family inner product, including the normalization by the raw
angular mass and the conjugation of the first Hilbert argument. -/
theorem sourceUnitFamily_inner_synthesis {n : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (i : Fin n) (a : Fin n → ℂ) :
    inner ℂ (sourceUnitFamily α hα0 hα1 i)
      (finiteSynthesis (sourceUnitFamily α hα0 hα1) a) =
      (sourceWeightMass α : ℂ)⁻¹ *
        (∫ θ : ℝ in Set.Icc (-Real.pi) Real.pi,
          sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ *
            starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
              starRingEnd ℂ (sourceCircle θ ^ i.val)) := by
  have hscale : starRingEnd ℂ ((Real.sqrt (sourceWeightMass α) : ℂ)⁻¹) *
      (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹ = (sourceWeightMass α : ℂ)⁻¹ := by
    rw [Complex.conj_inv, Complex.conj_ofReal, ← pow_two, inv_pow, ← Complex.ofReal_pow,
      Real.sq_sqrt (sourceWeightMass_nonneg α)]
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [sourceUnitFamily_coe hα0 hα1 i,
    sourceUnitFamily_synthesis_ae hα0 hα1 a] with θ hi ha
  rw [RCLike.inner_apply', hi, ha]
  simp only [map_mul]
  calc
    _ = (starRingEnd ℂ ((Real.sqrt (sourceWeightMass α) : ℂ)⁻¹) *
        (Real.sqrt (sourceWeightMass α) : ℂ)⁻¹) *
        (sourceWeightFactor α (sourceCircle θ) * sourcePolynomial a θ *
          starRingEnd ℂ (sourceWeightFactor α (sourceCircle θ)) *
            starRingEnd ℂ (sourceCircle θ ^ i.val)) := by ring
    _ = _ := by rw [hscale]

end ProofProject
