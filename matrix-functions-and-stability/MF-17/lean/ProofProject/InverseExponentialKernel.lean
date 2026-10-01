import ProofProject.GeneratorExponentialSeries
import ProofProject.GammaKernelSeries
import ProofProject.SemigroupKernelSeries

/-!
# The actual inverse exponential as a Bessel kernel integral

The normalized Gamma powers, their absolutely summable scalar coefficients,
and the strong kernel-summation theorem discharge every representation premise.
The final vector integral uses the original stable semigroup and is integrable
for every positive time, before any asymptotic estimate for the Bessel kernel.
-/

noncomputable section

open MeasureTheory Set

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {T : StableSemigroup M H} {B : H →L[ℂ] H}

theorem IsGeneratorInverse.exponential_term_eq_weightedGammaOperator
    (hB : IsGeneratorInverse T B) (t : ℝ) (ht : 0 < t) (n : ℕ) :
    (((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1) =
      (BoundedSemigroup.ofStableRescale T t ht).kernelOperator (weightedGammaTerm t n)
        (weightedGammaTerm_integrable n ht) := by
  rw [hB.neg_pow_succ_eq_gammaOperator n t ht]
  ext x
  simp only [smul_apply, BoundedSemigroup.kernelOperator_apply]
  rw [← integral_smul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by simp only [weightedGammaTerm, mul_smul]

/-- The inverse exponential has the exact actual damped-Bessel representation. -/
theorem IsGeneratorInverse.inverseEvolution_eq_one_sub_besselKernelOperator
    (hB : IsGeneratorInverse T B) (t : ℝ) (ht : 0 < t) :
    inverseEvolution B t = 1 -
      (BoundedSemigroup.ofStableRescale T t ht).kernelOperator (besselDampedKernel t)
        (besselDampedKernel_integrable ht) := by
  let S := BoundedSemigroup.ofStableRescale T t ht
  have hsum : Integrable (fun u : ℝ => ∑' n : ℕ, weightedGammaTerm t n u) := by
    apply (besselDampedKernel_integrable ht).neg.congr
    exact Filter.Eventually.of_forall (fun u => (tsum_weightedGammaTerm ht u).symm)
  have hop : S.kernelOperator (fun u : ℝ => ∑' n : ℕ, weightedGammaTerm t n u) hsum =
      -S.kernelOperator (besselDampedKernel t) (besselDampedKernel_integrable ht) := by
    ext x
    simp only [BoundedSemigroup.kernelOperator_apply, neg_apply]
    simp_rw [tsum_weightedGammaTerm ht, neg_smul]
    exact integral_neg _
  calc
    _ = 1 + ∑' n : ℕ,
        (((-t) ^ (n + 1) / ((n + 1).factorial : ℝ) : ℝ) : ℂ) • (-B) ^ (n + 1) :=
      inverseEvolution_eq_one_add_tsum_neg_powers B t
    _ = 1 + ∑' n : ℕ, S.kernelOperator (weightedGammaTerm t n)
        (weightedGammaTerm_integrable n ht) := by
      congr 1
      apply tsum_congr
      intro n
      exact hB.exponential_term_eq_weightedGammaOperator t ht n
    _ = 1 + S.kernelOperator (fun u : ℝ => ∑' n : ℕ, weightedGammaTerm t n u) hsum := by
      rw [S.kernelOperator_tsum (fun n => weightedGammaTerm_integrable n ht)
        (weightedGammaTerm_integral_norm_summable ht)
        (fun u => (weightedGammaTerm_hasSum ht u).summable) hsum]
    _ = _ := by rw [hop, sub_eq_add_neg]

private theorem besselDampedKernel_rescaledOrbit_eq
    (T : StableSemigroup M H) (t : ℝ) (ht : 0 < t) (x : H) (u : ℝ) :
    besselDampedKernel t u • (BoundedSemigroup.ofStableRescale T t ht).positiveOrbit x u =
      (Ioi (0 : ℝ)).indicator
        (fun u => (besselKernel u : ℂ) • T.op (u / t) x) u := by
  by_cases hu : 0 < u
  · rw [besselDampedKernel_of_pos t hu, BoundedSemigroup.positiveOrbit,
      max_eq_left hu.le, BoundedSemigroup.ofStableRescale_op,
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu), smul_apply,
      smul_smul, ← Complex.ofReal_mul]
    have he : Real.exp (-u / t) * Real.exp (u / t) = 1 := by
      rw [← Real.exp_add, show -u / t + u / t = 0 by ring, Real.exp_zero]
    have hc : (Real.exp (-u / t) * besselKernel u) * Real.exp (u / t) =
        besselKernel u := by
      calc
        _ = besselKernel u * (Real.exp (-u / t) * Real.exp (u / t)) := by ring
        _ = besselKernel u := by rw [he, mul_one]
    rw [hc]
  · rw [besselDampedKernel_of_nonpos t (le_of_not_gt hu), zero_smul,
      indicator_of_notMem (show u ∉ Ioi (0 : ℝ) from hu)]

/-- The original-semigroup Bessel integral is genuinely integrable, with no
asymptotic or conditional convergence assumption. -/
theorem StableSemigroup.besselKernel_orbit_integrable (T : StableSemigroup M H)
    (t : ℝ) (ht : 0 < t) (x : H) :
    IntegrableOn (fun u : ℝ => (besselKernel u : ℂ) • T.op (u / t) x) (Ioi 0) := by
  have h := (BoundedSemigroup.ofStableRescale T t ht).kernelOrbit_integrable
    (besselDampedKernel_integrable ht) x
  have heq : (fun u : ℝ => besselDampedKernel t u •
      (BoundedSemigroup.ofStableRescale T t ht).positiveOrbit x u) =
      (Ioi (0 : ℝ)).indicator (fun u => (besselKernel u : ℂ) • T.op (u / t) x) :=
    funext (besselDampedKernel_rescaledOrbit_eq T t ht x)
  rw [heq, integrable_indicator_iff measurableSet_Ioi] at h
  exact h

/-- Strong positive-half-line representation of the exact target exponential. -/
theorem IsGeneratorInverse.inverseEvolution_apply_eq_besselIntegral
    (hB : IsGeneratorInverse T B) (t : ℝ) (ht : 0 < t) (x : H) :
    inverseEvolution B t x = x -
      ∫ u : ℝ in Ioi 0, (besselKernel u : ℂ) • T.op (u / t) x := by
  rw [hB.inverseEvolution_eq_one_sub_besselKernelOperator t ht,
    sub_apply, BoundedSemigroup.kernelOperator_apply]
  change x - (∫ u : ℝ, besselDampedKernel t u •
    (BoundedSemigroup.ofStableRescale T t ht).positiveOrbit x u) = _
  simp_rw [besselDampedKernel_rescaledOrbit_eq T t ht x]
  rw [integral_indicator measurableSet_Ioi]

end ProofProject
