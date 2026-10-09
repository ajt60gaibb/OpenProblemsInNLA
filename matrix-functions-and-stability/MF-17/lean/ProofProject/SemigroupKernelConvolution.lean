import ProofProject.SemigroupKernelOperator
import Mathlib.Analysis.Convolution

/-!
# Composition of strong semigroup kernel operators

Scalar convolution is identified with composition only for kernels supported
at nonnegative times. Fubini is justified in the Hilbert space after applying
the orbit to a vector; no operator-valued integral occurs.
-/

noncomputable section

open MeasureTheory Set Filter

namespace ProofProject

def kernelConvolution (k l : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∫ s, k s * l (v - s)

theorem kernelConvolution_integrable {k l : ℝ → ℂ}
    (hk : Integrable k) (hl : Integrable l) :
    Integrable (kernelConvolution k l) := by
  simpa only [kernelConvolution, MeasureTheory.convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul] using!
    hk.integrable_convolution (ContinuousLinearMap.lsmul ℂ ℂ) hl

theorem kernelConvolution_eq_zero_of_neg {k l : ℝ → ℂ}
    (hk : ∀ s < 0, k s = 0) (hl : ∀ s < 0, l s = 0)
    {v : ℝ} (hv : v < 0) : kernelConvolution k l v = 0 := by
  apply integral_eq_zero_of_ae
  exact Eventually.of_forall fun s => by
    dsimp only [Pi.zero_apply]
    by_cases hs : s < 0
    · rw [hk s hs, zero_mul]
    · rw [hl (v - s) (by linarith), mul_zero]

universe u

/-- A convolution may be paired with any bounded continuous vector function. -/
theorem kernelConvolution_smul_integral
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l)
    (F : ℝ → H) (hF : Continuous F) {C : ℝ} (hbound : ∀ v, ‖F v‖ ≤ C) :
    (∫ v, kernelConvolution k l v • F v) =
      ∫ s, k s • ∫ t, l t • F (s + t) := by
  have hg : Integrable (fun p : ℝ × ℝ => k p.2 * l (p.1 - p.2))
      (volume.prod volume) := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      hk.convolution_integrand (ContinuousLinearMap.lsmul ℂ ℂ) hl
  have hi : Integrable (fun p : ℝ × ℝ =>
      (k p.2 * l (p.1 - p.2)) • F p.1) (volume.prod volume) :=
    hg.smul_bdd C (hF.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hbound p.1)
  calc
    _ = ∫ v, ∫ s, (k s * l (v - s)) • F v := by
      simp only [kernelConvolution, integral_smul_const]
    _ = ∫ s, ∫ v, (k s * l (v - s)) • F v := integral_integral_swap hi
    _ = ∫ s, ∫ t, k s • (l t • F (s + t)) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by
        have ht := integral_add_right_eq_self (μ := volume)
          (fun v : ℝ => (k s * l (v - s)) • F v) s
        simpa only [add_sub_cancel_right, add_sub_cancel_left, mul_smul, add_comm]
          using ht.symm
    _ = _ := by simp only [integral_smul]

namespace BoundedSemigroup

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem kernelOperator_add (S : BoundedSemigroup M H)
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l) :
    S.kernelOperator (k + l) (hk.add hl) =
      S.kernelOperator k hk + S.kernelOperator l hl := by
  ext x
  simp only [kernelOperator_apply, add_apply, Pi.add_apply, add_smul]
  exact integral_add (S.kernelOrbit_integrable hk x) (S.kernelOrbit_integrable hl x)

theorem kernelOperator_sub (S : BoundedSemigroup M H)
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l) :
    S.kernelOperator (k - l) (hk.sub hl) =
      S.kernelOperator k hk - S.kernelOperator l hl := by
  ext x
  simp only [kernelOperator_apply, sub_apply, Pi.sub_apply, sub_smul]
  exact integral_sub (S.kernelOrbit_integrable hk x) (S.kernelOrbit_integrable hl x)

theorem kernelOperator_smul (S : BoundedSemigroup M H)
    (c : ℂ) {k : ℝ → ℂ} (hk : Integrable k) :
    S.kernelOperator (c • k) (hk.smul c) = c • S.kernelOperator k hk := by
  ext x
  simp only [kernelOperator_apply, smul_apply, Pi.smul_apply,
    smul_eq_mul, mul_smul, integral_smul]

/-- All scalar kernel operators commute, even before restricting supports. -/
theorem kernelOperator_commute (S : BoundedSemigroup M H)
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l) :
    (S.kernelOperator k hk).comp (S.kernelOperator l hl) =
      (S.kernelOperator l hl).comp (S.kernelOperator k hk) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  rw [kernelOperator_apply, kernelOperator_apply S k hk]
  rw [← (S.kernelOperator l hl).integral_comp_comm (S.kernelOrbit_integrable hk x)]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    dsimp only
    rw [map_smul]
    congr 1
    exact congrArg (fun A : H →L[ℂ] H => A x)
      (S.kernelOperator_commutes l hl (le_max_right s 0))

/-- Convolution of nonnegative-time kernels is genuine operator composition. -/
theorem kernelOperator_convolution (S : BoundedSemigroup M H)
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l)
    (hks : ∀ s < 0, k s = 0) (hls : ∀ s < 0, l s = 0) :
    S.kernelOperator (kernelConvolution k l) (kernelConvolution_integrable hk hl) =
      (S.kernelOperator k hk).comp (S.kernelOperator l hl) := by
  ext x
  rw [kernelOperator_apply, kernelConvolution_smul_integral hk hl
    (S.positiveOrbit x) (S.positiveOrbit_continuous x) (S.positiveOrbit_norm_le x)]
  simp only [ContinuousLinearMap.comp_apply, kernelOperator_apply]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    dsimp only [Pi.zero_apply]
    by_cases hs : s < 0
    · simp only [hks s hs, zero_smul]
    have hs0 : 0 ≤ s := le_of_not_gt hs
    rw [positiveOrbit, max_eq_left hs0,
      ← (S.op s).integral_comp_comm (S.kernelOrbit_integrable hl x)]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun t => by
      dsimp only
      by_cases ht : t < 0
      · simp only [hls t ht, zero_smul, map_zero]
      have ht0 : 0 ≤ t := le_of_not_gt ht
      simp only [positiveOrbit, max_eq_left ht0, max_eq_left (add_nonneg hs0 ht0),
        map_smul, S.add s t hs0 ht0, ContinuousLinearMap.comp_apply]

end BoundedSemigroup

end ProofProject
