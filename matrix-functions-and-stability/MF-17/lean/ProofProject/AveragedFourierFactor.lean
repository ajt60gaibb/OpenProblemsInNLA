import ProofProject.AveragedFourierOperator
import ProofProject.AveragingTriangle
import Mathlib.Analysis.Convolution

/-!
# The two averaged Fourier factors and the convolution window

The pairing is expanded through strong vector integrals. Fubini is applied
only to a scalar integrable function. In Mathlib's inner-product convention
the adjoint factor is the first argument, so the combined phase is negative.
-/

noncomputable section

open MeasureTheory Set Filter FourierTransform

namespace ProofProject

private theorem integral_averagingWindow_smul (N : ℝ) (F : ℝ → ℂ) :
    (∫ s, averagingWindow N s • F s) =
      ∫ s in Icc (N / 2) (3 * N / 2), (Real.sqrt N)⁻¹ • F s := by
  rw [averagingWindow_smul_eq_indicator, integral_indicator measurableSet_Icc]

/-- The genuine convolution integral paired with a bounded continuous scalar
function. Its Fubini hypothesis follows from the two `L¹` windows. -/
theorem averagingWindow_convolution_test (N : ℝ) (F : ℝ → ℂ)
    (hF : Continuous F) {C : ℝ} (hbound : ∀ v, ‖F v‖ ≤ C) :
    (∫ v, (∫ s, averagingWindow N s * averagingWindow N (v - s)) • F v) =
      ∫ s in Icc (N / 2) (3 * N / 2),
        ∫ t in Icc (N / 2) (3 * N / 2),
          (Real.sqrt N)⁻¹ • ((Real.sqrt N)⁻¹ • F (s + t)) := by
  have hg : Integrable (fun p : ℝ × ℝ =>
      averagingWindow N p.2 * averagingWindow N (p.1 - p.2)) (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (averagingWindow_integrable N).convolution_integrand
        (ContinuousLinearMap.lsmul ℝ ℝ) (averagingWindow_integrable N)
  have hi : Integrable (fun p : ℝ × ℝ =>
      (averagingWindow N p.2 * averagingWindow N (p.1 - p.2)) • F p.1)
      (volume.prod volume) := by
    exact hg.smul_bdd C (hF.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hbound p.1)
  calc
    _ = ∫ v, ∫ s,
        (averagingWindow N s * averagingWindow N (v - s)) • F v := by
      simp only [integral_smul_const]
    _ = ∫ s, ∫ v,
        (averagingWindow N s * averagingWindow N (v - s)) • F v :=
      integral_integral_swap hi
    _ = ∫ s, ∫ t,
        averagingWindow N s • (averagingWindow N t • F (s + t)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        have ht := integral_add_right_eq_self (μ := volume)
          (fun v : ℝ => (averagingWindow N s * averagingWindow N (v - s)) • F v) s
        simpa only [add_sub_cancel_right, add_sub_cancel_left, mul_smul, add_comm] using ht.symm
    _ = ∫ s, averagingWindow N s • ∫ t, averagingWindow N t • F (s + t) := by
      simp only [integral_smul]
    _ = ∫ s in Icc (N / 2) (3 * N / 2),
        (Real.sqrt N)⁻¹ • ∫ t in Icc (N / 2) (3 * N / 2),
          (Real.sqrt N)⁻¹ • F (s + t) := by
      rw [integral_averagingWindow_smul]
      simp_rw [integral_averagingWindow_smul]
    _ = _ := by simp only [integral_smul]

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Expanding the actual two operator averages on their compact windows. -/
theorem averagedFourierOperator_pairing_double (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (ξ a : ℝ) (ha : 0 ≤ a) (x y : H) :
    inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
      (S.op a (S.averagedFourierOperator N hN ξ x)) =
      ∫ s in Icc (N / 2) (3 * N / 2),
        ∫ t in Icc (N / 2) (3 * N / 2),
          averagingFourierKernel N ξ s * averagingFourierKernel N ξ t *
            inner ℂ y (S.op (s + t + a) x) := by
  have hint (z : H) : IntegrableOn
      (fun s => averagingFourierKernel N ξ s • S.op s z)
      (Icc (N / 2) (3 * N / 2)) :=
    intervalOperatorIntegral_integrable S.op (averagingFourierKernel N ξ)
      (N / 2) (3 * N / 2) (averagingFourierKernel_continuous N ξ).continuousOn
      (S.averagingInterval_continuous hN) z
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left,
    averagedFourierOperator_apply]
  have hinner := (innerSL ℂ y).integral_comp_comm
    (hint (S.op a (S.averagedFourierOperator N hN ξ x)))
  simp only [innerSL_apply_apply] at hinner
  rw [← hinner]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  have hs0 : 0 ≤ s := averagingInterval_nonneg hN hs
  let L : H →L[ℂ] ℂ := (innerSL ℂ y).comp ((S.op s).comp (S.op a))
  have hLi := L.integral_comp_comm (hint x)
  change inner ℂ y (averagingFourierKernel N ξ s •
    S.op s (S.op a (S.averagedFourierOperator N hN ξ x))) = _
  rw [inner_smul_right, averagedFourierOperator_apply]
  change averagingFourierKernel N ξ s * L
    (∫ t in Icc (N / 2) (3 * N / 2), averagingFourierKernel N ξ t • S.op t x) = _
  rw [← hLi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  have ht0 : 0 ≤ t := averagingInterval_nonneg hN ht
  have hopp : S.op s (S.op a (S.op t x)) = S.op (s + t + a) x := by
    rw [show s + t + a = s + (a + t) by ring,
      S.add s (a + t) hs0 (add_nonneg ha ht0), S.add a t ha ht0]
    rfl
  simp only [L, ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply,
    hopp]
  ring

omit [CompleteSpace H] in
private theorem positive_shift_orbit_continuous (S : BoundedSemigroup M H)
    {a : ℝ} (ha : 0 ≤ a) (x : H) :
    Continuous (fun v : ℝ => S.op (max v 0 + a) x) := by
  exact (S.strong_continuous x).comp_continuous
    ((continuous_id.max continuous_const).add_const a)
    (fun v => add_nonneg (le_max_right v 0) ha)

omit [CompleteSpace H] in
/-- The actual scalar correlation has compact support, despite arbitrary values
of the semigroup at negative times. -/
theorem integrable_averagingTriangle_pairing (S : BoundedSemigroup M H)
    {N a : ℝ} (hN : 0 < N) (ha : 0 ≤ a) (x y : H) :
    Integrable (fun v : ℝ => (averagingTriangle N v : ℂ) *
      inner ℂ y (S.op (v + a) x)) := by
  have heq : (fun v : ℝ => (averagingTriangle N v : ℂ) *
      inner ℂ y (S.op (v + a) x)) =
      fun v : ℝ => (averagingTriangle N v : ℂ) *
        inner ℂ y (S.op (max v 0 + a) x) := by
    funext v
    by_cases hv : 0 ≤ v
    · rw [max_eq_left hv]
    · rw [averagingTriangle_eq_zero_of_le hN (by linarith)]
      simp
  rw [heq]
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp (averagingTriangle_continuous hN)).mul
      ((innerSL ℂ y).continuous.comp (S.positive_shift_orbit_continuous ha x))
  · apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro v hv
    apply averagingTriangle_support_subset hN
    intro hz
    exact hv (by simp [hz])

/-- The two strong operator integrals combine into the actual triangular
convolution, with Mathlib's negative Fourier phase. -/
theorem averagedFourierOperator_pairing_triangle (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (ξ a : ℝ) (ha : 0 ≤ a) (x y : H) :
    inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
      (S.op a (S.averagedFourierOperator N hN ξ x)) =
      ∫ v, (averagingTriangle N v : ℂ) *
        (Real.fourierChar (-(v * ξ)) : ℂ) * inner ℂ y (S.op (v + a) x) := by
  let F : ℝ → ℂ := fun v => (Real.fourierChar (-(v * ξ)) : ℂ) *
    inner ℂ y (S.op (max v 0 + a) x)
  have hF : Continuous F :=
    (continuous_subtype_val.comp
      (Real.continuous_fourierChar.comp (continuous_id.mul_const ξ).neg)).mul
        ((innerSL ℂ y).continuous.comp (S.positive_shift_orbit_continuous ha x))
  have hFb (v : ℝ) : ‖F v‖ ≤ ‖y‖ * (M * ‖x‖) := by
    simp only [F, norm_mul, Circle.norm_coe, one_mul]
    exact (norm_inner_le_norm y _).trans (mul_le_mul_of_nonneg_left
      (((S.op (max v 0 + a)).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right
          (S.bound _ (add_nonneg (le_max_right v 0) ha)) (norm_nonneg x))) (norm_nonneg y))
  rw [S.averagedFourierOperator_pairing_double N hN ξ a ha x y]
  calc
    _ = ∫ s in Icc (N / 2) (3 * N / 2),
        ∫ t in Icc (N / 2) (3 * N / 2),
          (Real.sqrt N)⁻¹ • ((Real.sqrt N)⁻¹ • F (s + t)) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      apply setIntegral_congr_fun measurableSet_Icc
      intro t ht
      have hst : 0 ≤ s + t := add_nonneg
        (averagingInterval_nonneg hN hs) (averagingInterval_nonneg hN ht)
      have hchar : (Real.fourierChar (-(s * ξ)) : ℂ) *
          (Real.fourierChar (-(t * ξ)) : ℂ) =
          (Real.fourierChar (-((s + t) * ξ)) : ℂ) := by
        rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul]
        congr 2
        ring
      simp only [F, max_eq_left hst, averagingFourierKernel,
        Complex.real_smul]
      calc
        _ = (((Real.sqrt N)⁻¹ : ℝ) : ℂ) * (((Real.sqrt N)⁻¹ : ℝ) : ℂ) *
            ((Real.fourierChar (-(s * ξ)) : ℂ) *
              (Real.fourierChar (-(t * ξ)) : ℂ)) *
                inner ℂ y (S.op (s + t + a) x) := by ring
        _ = _ := by rw [hchar]; ring
    _ = ∫ v, averagingTriangle N v • F v :=
      (averagingWindow_convolution_test N F hF hFb).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v => by
        change averagingTriangle N v • F v =
          (averagingTriangle N v : ℂ) *
            (Real.fourierChar (-(v * ξ)) : ℂ) * inner ℂ y (S.op (v + a) x)
        by_cases hv : 0 ≤ v
        · simp only [F, max_eq_left hv, Complex.real_smul]
          ring
        · rw [averagingTriangle_eq_zero_of_le hN (by linarith)]
          simp

/-- Fourier-transform form of the factor identity; the correlation is genuinely
integrable by `integrable_averagingTriangle_pairing`. -/
theorem averagedFourierOperator_pairing_fourier (S : BoundedSemigroup M H)
    (N : ℝ) (hN : 0 < N) (ξ a : ℝ) (ha : 0 ≤ a) (x y : H) :
    inner ℂ (star (S.averagedFourierOperator N hN ξ) y)
      (S.op a (S.averagedFourierOperator N hN ξ x)) =
      𝓕 (fun v : ℝ => (averagingTriangle N v : ℂ) *
        inner ℂ y (S.op (v + a) x)) ξ := by
  rw [S.averagedFourierOperator_pairing_triangle N hN ξ a ha x y, Real.fourier_real_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun v => by
    simp only [Circle.smul_def, smul_eq_mul]
    ring

end BoundedSemigroup

end ProofProject
