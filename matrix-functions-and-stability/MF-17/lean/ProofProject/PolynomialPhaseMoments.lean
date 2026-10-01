import ProofProject.RationalCircleAngle
import ProofProject.FiniteHankelForm

/-!
# Negative moments of a polynomial phase

For a polynomial `h` that is zero-free on the closed disk, the phase
`conj(h)/h` has no Fourier coefficient below `-h.natDegree`. This follows by
uniform polynomial approximation of `1/h`, with all integrations performed
against the normalized Haar probability measure on the period-one circle.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

private lemma integrable_circle_of_continuous {f : AddCircle (1 : ℝ) → ℂ}
    (hf : Continuous f) : Integrable f AddCircle.haarAddCircle := by
  simpa only [integrableOn_univ] using
    hf.continuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle) isCompact_univ

lemma polynomialCircle_eval_sum (h : Polynomial ℂ) (z : AddCircle (1 : ℝ)) :
    h.eval (fourier 1 z) = ∑ j ∈ h.support, h.coeff j * fourier (j : ℤ) z := by
  simp only [circleGram_fourier_nat, Polynomial.eval_eq_sum, Polynomial.sum_def]

/-- Extraction of a conjugated polynomial coefficient with no normalization
factor, since Haar measure has total mass one. -/
theorem polynomialCircle_conj_moment (h : Polynomial ℂ) (l : ℕ) :
    (∫ z : AddCircle (1 : ℝ), starRingEnd ℂ (h.eval (fourier 1 z)) *
      fourier (l : ℤ) z ∂AddCircle.haarAddCircle) = starRingEnd ℂ (h.coeff l) := by
  classical
  have ht (j : ℕ) :
      (∫ z : AddCircle (1 : ℝ),
        starRingEnd ℂ (h.coeff j * fourier (j : ℤ) z) * fourier (l : ℤ) z
          ∂AddCircle.haarAddCircle) =
        if j = l then starRingEnd ℂ (h.coeff j) else 0 := by
    calc
      _ = starRingEnd ℂ (h.coeff j) *
          ∫ z : AddCircle (1 : ℝ), fourier (l : ℤ) z *
            starRingEnd ℂ (fourier (j : ℤ) z) ∂AddCircle.haarAddCircle := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by dsimp only; rw [map_mul]; ring
      _ = _ := by rw [finiteCircle_character_inner]; simp
  have hi (j : ℕ) : Integrable (fun z : AddCircle (1 : ℝ) =>
      starRingEnd ℂ (h.coeff j * fourier (j : ℤ) z) * fourier (l : ℤ) z)
        AddCircle.haarAddCircle := by
    apply integrable_circle_of_continuous
    simpa only [starRingEnd_apply, Pi.mul_def] using!
      ((continuous_const.mul (fourier (j : ℤ)).continuous).star.mul
        (fourier (l : ℤ)).continuous : Continuous
          (fun z : AddCircle (1 : ℝ) => star (h.coeff j * fourier (j : ℤ) z) *
            fourier (l : ℤ) z))
  simp_rw [polynomialCircle_eval_sum, map_sum, Finset.sum_mul]
  rw [integral_finsetSum h.support (fun j _ => hi j)]
  simp_rw [ht]
  by_cases hl : l ∈ h.support
  · simp [hl]
  · have hc : h.coeff l = 0 := by simpa only [Polynomial.mem_support_iff, not_not] using hl
    simp [hl, hc]

/-- The finite coefficient formula before passing to a reciprocal limit. -/
theorem polynomialCircle_conj_mul_moment (h q : Polynomial ℂ) (l : ℕ) :
    (∫ z : AddCircle (1 : ℝ), starRingEnd ℂ (h.eval (fourier 1 z)) *
      q.eval (fourier 1 z) * fourier (l : ℤ) z ∂AddCircle.haarAddCircle) =
      ∑ j ∈ q.support, q.coeff j * starRingEnd ℂ (h.coeff (l + j)) := by
  have hpoint (z : AddCircle (1 : ℝ)) :
      starRingEnd ℂ (h.eval (fourier 1 z)) * q.eval (fourier 1 z) *
        fourier (l : ℤ) z =
      ∑ j ∈ q.support, q.coeff j *
        (starRingEnd ℂ (h.eval (fourier 1 z)) * fourier ((l + j : ℕ) : ℤ) z) := by
    rw [polynomialCircle_eval_sum q]
    simp only [Finset.mul_sum, Finset.sum_mul, Nat.cast_add, fourier_add]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hi (j : ℕ) : Integrable (fun z : AddCircle (1 : ℝ) =>
      q.coeff j * (starRingEnd ℂ (h.eval (fourier 1 z)) *
        fourier ((l + j : ℕ) : ℤ) z)) AddCircle.haarAddCircle := by
    apply integrable_circle_of_continuous
    simpa only [starRingEnd_apply, Pi.mul_def, Function.comp_def] using!
      (continuous_const : Continuous (fun _ : AddCircle (1 : ℝ) => q.coeff j)).mul
        ((h.continuous.comp (fourier 1).continuous).star.mul
        (fourier ((l + j : ℕ) : ℤ)).continuous)
  simp_rw [hpoint]
  rw [integral_finsetSum q.support (fun j _ => hi j)]
  simp only [integral_const_mul, polynomialCircle_conj_moment]

theorem polynomialCircle_conj_mul_moment_eq_zero (h q : Polynomial ℂ) {l : ℕ}
    (hl : h.natDegree < l) :
    (∫ z : AddCircle (1 : ℝ), starRingEnd ℂ (h.eval (fourier 1 z)) *
      q.eval (fourier 1 z) * fourier (l : ℤ) z ∂AddCircle.haarAddCircle) = 0 := by
  rw [polynomialCircle_conj_mul_moment]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega : h.natDegree < l + j)]
  simp

/-- Supremum-norm convergence of continuous circle functions passes to their
complex integrals. The proof uses the continuous inclusion into circle L². -/
theorem circleContinuous_integral_tendsto {F : ℕ → C(AddCircle (1 : ℝ), ℂ)}
    {f : C(AddCircle (1 : ℝ), ℂ)} (hF : Tendsto F atTop (𝓝 f)) :
    Tendsto (fun N => ∫ z : AddCircle (1 : ℝ), F N z ∂AddCircle.haarAddCircle)
      atTop (𝓝 (∫ z : AddCircle (1 : ℝ), f z ∂AddCircle.haarAddCircle)) := by
  let J := ContinuousMap.toLp (E := ℂ) 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) ℂ
  have hJ : Tendsto (fun N => J (F N)) atTop (𝓝 (J f)) :=
    J.continuous.tendsto f |>.comp hF
  have he (g : C(AddCircle (1 : ℝ), ℂ)) :
      inner ℂ (J (1 : C(AddCircle (1 : ℝ), ℂ))) (J g) =
        ∫ z : AddCircle (1 : ℝ), g z ∂AddCircle.haarAddCircle := by
    rw [ContinuousMap.inner_toLp]
    simp
  simpa only [he] using (tendsto_const_nhds.inner hJ :
    Tendsto (fun N => inner ℂ (J (1 : C(AddCircle (1 : ℝ), ℂ))) (J (F N)))
      atTop (𝓝 (inner ℂ (J (1 : C(AddCircle (1 : ℝ), ℂ))) (J f))))

/-- The `k`th negative phase moment corresponds to frequency `-k-1`, so it
vanishes already when `h.natDegree ≤ k`. -/
theorem polynomialCirclePhase_negativeMoment_eq_zero {h : Polynomial ℂ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) {k : ℕ}
    (hk : h.natDegree ≤ k) :
    phaseNegativeMoment (polynomialCirclePhase h) k = 0 := by
  obtain ⟨r, hr⟩ := exists_polynomial_tendstoUniformlyOn_reciprocal h hh
  let H := polynomialCircleMap h
  let R := polynomialReciprocalCircleMap h hh
  let RN := fun N => polynomialCircleMap (r N)
  let F := fun N => (star H * RN N) * fourier ((k : ℤ) + 1)
  let f := (star H * R) * fourier ((k : ℤ) + 1)
  have hR : Tendsto RN atTop (𝓝 R) := polynomialCircleMap_reciprocal_tendsto h hh hr
  have hF : Tendsto F atTop (𝓝 f) :=
    (tendsto_const_nhds.mul hR).mul_const _
  have hi := circleContinuous_integral_tendsto hF
  have hzero (N : ℕ) :
      (∫ z : AddCircle (1 : ℝ), F N z ∂AddCircle.haarAddCircle) = 0 := by
    change (∫ z : AddCircle (1 : ℝ),
      starRingEnd ℂ (h.eval (fourier 1 z)) * (r N).eval (fourier 1 z) *
        fourier ((k : ℤ) + 1) z ∂AddCircle.haarAddCircle) = 0
    simpa only [Nat.cast_add, Nat.cast_one] using
      polynomialCircle_conj_mul_moment_eq_zero h (r N) (by omega : h.natDegree < k + 1)
  have he : (∫ z : AddCircle (1 : ℝ), f z ∂AddCircle.haarAddCircle) = 0 :=
    tendsto_nhds_unique hi (by simp only [hzero]; exact tendsto_const_nhds)
  simpa only [phaseNegativeMoment, polynomialCirclePhase, div_eq_mul_inv, f, H, R,
    polynomialCircleMap, polynomialReciprocalCircleMap, ContinuousMap.mul_apply,
    ContinuousMap.star_apply, ContinuousMap.coe_mk, starRingEnd_apply] using he

/-- Multiplying by the original polynomial cancels the reciprocal phase and
recovers the conjugated coefficient exactly. -/
theorem polynomialCirclePhase_mul_moment (h : Polynomial ℂ)
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) (l : ℕ) :
    (∫ z : AddCircle (1 : ℝ), h.eval (fourier 1 z) * polynomialCirclePhase h z *
      fourier (l : ℤ) z ∂AddCircle.haarAddCircle) = starRingEnd ℂ (h.coeff l) := by
  convert polynomialCircle_conj_moment h l using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    have hz := hh _ (le_of_eq (finiteCircle_fourier_norm 1 z))
    dsimp only [polynomialCirclePhase]
    field_simp [hz]

end ProofProject
