import ProofProject.TransformedAmplitudeBounds
import ProofProject.PowerTailIntegral
import ProofProject.SourceOscillatoryOperator
import ProofProject.ResolventOperatorIdentity

/-!
# Resolvent deletion and retention of a signed oscillatory kernel

The transformed amplitude bounds supply the one-interval theorem's premises.
The primitive remainder is estimated by absolute integration. The resulting
operator inequalities retain the exact support and characteristic scales.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace ProofProject

private theorem amplitude_compact_of_bounds {a : ℝ → ℂ} {l r : ℝ}
    (hl : ∀ u < l, a u = 0) (hr : ∀ u, r < u → a u = 0) : HasCompactSupport a := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro u hu
  constructor
  · by_contra h
    exact hu (hl u (lt_of_not_ge h))
  · by_contra h
    exact hu (hr u (lt_of_not_ge h))

private theorem bounds_through_two {a : ℝ → ℂ} {A : ℝ}
    (h : ∀ n ≤ 2, ∀ u > 0, ‖iteratedDeriv n a u‖ ≤ A * u ^ (-3 / 4 - (n : ℝ))) :
    (∀ u > 0, ‖a u‖ ≤ A * u ^ (-3 / 4 : ℝ)) ∧
    (∀ u > 0, ‖deriv a u‖ ≤ A * u ^ (-3 / 4 - 1 : ℝ)) ∧
    (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A * u ^ (-3 / 4 - 2 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using h 0 (by omega)
  · simpa only [iteratedDeriv_one, Nat.cast_one] using h 1 (by omega)
  · simpa only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.cast_ofNat] using h 2 (by omega)

universe u

private theorem kernelOperator_congr {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {M : ℝ} (S : BoundedSemigroup M H)
    {k l : ℝ → ℂ} (hk : Integrable k) (hl : Integrable l) (heq : k = l) :
    S.kernelOperator k hk = S.kernelOperator l hl := by
  cases heq
  rfl

set_option maxHeartbeats 800000 in
/-- A single absolute oscillatory constant supplies both exact-scale resolvent
estimates, for both signs and arbitrary complete complex Hilbert spaces. -/
theorem exists_oscillatoryResolvent_bounds :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ℝ) (S : BoundedSemigroup M H) (N A : ℝ), 16 ≤ N → 0 ≤ A →
      ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ v < 2 * N, a v = 0) →
      (∀ v, 4 * N ^ (4 / 3 : ℝ) < v → a v = 0) →
      (∀ n ≤ 3, ∀ v > 0, ‖iteratedDeriv n a v‖ ≤ A * v ^ (-3 / 4 - (n : ℝ))) →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ r : ℝ, ∀ hr : 0 < r,
      ∀ hk : Integrable (oscillatoryKernel σ a),
        ‖S.resolventAverage r hr * S.kernelOperator (oscillatoryKernel σ a) hk‖ ≤
          (9 / 2) * C * M ^ 3 * (1 + M) * A * r * Real.sqrt (N ^ (4 / 3 : ℝ)) +
            6 * M ^ 2 * A * (2 * N) ^ (-1 / 4 : ℝ) ∧
        ‖(1 - S.resolventAverage r hr) * S.kernelOperator (oscillatoryKernel σ a) hk‖ ≤
          4 * C * M ^ 4 * A / (r * Real.sqrt N) := by
  obtain ⟨C, hC, hosc⟩ := exists_sourceOscillatoryKernelOperator_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ M S N A hN16 hA a ha hl hu hweights σ hσ r hr hk
  have hN : 0 < N := by linarith
  have hδ : 0 < 2 * N := by positivity
  have hcompact := amplitude_compact_of_bounds hl hu
  let b := signedPrimitiveAmplitude σ a
  let c := signedDerivativeAmplitude σ a
  let p := oscillatoryKernel σ b
  let d := oscillatoryKernel σ (deriv b)
  let k := oscillatoryKernel σ a
  have hb : ContDiff ℝ ∞ b := signedPrimitiveAmplitude_contDiff σ ha hδ hl
  have hc : ContDiff ℝ ∞ c := signedDerivativeAmplitude_contDiff σ ha hδ hl
  have hbl : ∀ v < 2 * N, b v = 0 := fun _ hv => signedPrimitiveAmplitude_eq_zero_of_lt σ hl hv
  have hbu : ∀ v, 4 * N ^ (4 / 3 : ℝ) < v → b v = 0 :=
    fun _ hv => signedPrimitiveAmplitude_eq_zero_of_gt σ hu hv
  have hcl : ∀ v < 2 * N, c v = 0 := fun _ hv => signedDerivativeAmplitude_eq_zero_of_lt σ hl hv
  have hcu : ∀ v, 4 * N ^ (4 / 3 : ℝ) < v → c v = 0 :=
    fun _ hv => signedDerivativeAmplitude_eq_zero_of_gt σ hu hv
  have hbcompact : HasCompactSupport b := signedPrimitiveAmplitude_hasCompactSupport σ hcompact
  have hccompact : HasCompactSupport c := signedDerivativeAmplitude_hasCompactSupport σ hcompact
  have hp : ContDiff ℝ ∞ p := oscillatoryKernel_contDiff σ hb hδ hbl
  have hpcompact : HasCompactSupport p := oscillatoryKernel_hasCompactSupport σ hbcompact
  obtain ⟨hpi, hpdi⟩ := smoothCompact_kernel_integrable hp hpcompact
  have hci : Integrable (oscillatoryKernel σ c) :=
    (oscillatoryKernel_continuous σ hc.continuous).integrable_of_hasCompactSupport
      (oscillatoryKernel_hasCompactSupport σ hccompact)
  have hdi : Integrable d :=
    (oscillatoryKernel_continuous σ (contDiff_infty_iff_deriv.mp hb).2.continuous).integrable_of_hasCompactSupport
      (oscillatoryKernel_hasCompactSupport σ hbcompact.deriv)
  have hbweights := signedPrimitiveAmplitude_weighted_bound ha hA hσ
    (Real.rpow_nonneg hN.le (4 / 3 : ℝ)) hu
    (fun n hn => hweights n (by omega))
  obtain ⟨hb0, hb1, hb2⟩ := bounds_through_two hbweights
  have hBp := hosc H M S N ((9 / 2) * A * Real.sqrt (N ^ (4 / 3 : ℝ))) hN16
    (by positivity) b hb hbl hbu hb0 hb1 hb2 σ hσ hpi
  have hcweights := signedDerivativeAmplitude_weighted_bound ha hA hσ (by linarith) hl hweights
  obtain ⟨hc0, hc1, hc2⟩ := bounds_through_two hcweights
  have hBc := hosc H M S N (4 * A / Real.sqrt N) hN16
    (by positivity) c hc hcl hcu hc0 hc1 hc2 σ hσ hci
  have hdl : ∀ v < 2 * N, d v = 0 := by
    intro v hv
    apply (oscillatoryKernel_eq_zero_iff σ _ v).mpr
    simpa only [iteratedDeriv_one] using iteratedDeriv_eq_zero_of_lower_support hbl hv 1
  have hdbound : ∀ v > 0, ‖d v‖ ≤ (3 / 2) * A * v ^ (-5 / 4 : ℝ) := by
    intro v hv
    rw [oscillatoryKernel_norm]
    apply norm_deriv_signedPrimitiveAmplitude_le ha hA hσ hv
    · simpa only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] using hweights 0 (by omega) v hv
    · convert hweights 1 (by omega) v hv using 1 <;> norm_num [iteratedDeriv_one]
  have hBd : ‖S.kernelOperator d hdi‖ ≤ 6 * M * A * (2 * N) ^ (-1 / 4 : ℝ) := by
    have hdint := integral_norm_le_source_power_tail hδ hdi hdl hdbound
    exact (S.kernelOperator_norm_le d hdi).trans
      ((mul_le_mul_of_nonneg_left hdint S.bound_nonneg).trans_eq (by ring))
  have hkdiff : ContDiff ℝ ∞ k := oscillatoryKernel_contDiff σ ha hδ hl
  have hkcompact : HasCompactSupport k := oscillatoryKernel_hasCompactSupport σ hcompact
  have hkdi : Integrable (deriv k) := (smoothCompact_kernel_integrable hkdiff hkcompact).2
  have hkeq : k = deriv p - d :=
    oscillatoryKernel_eq_deriv_primitive_sub σ hσ ha hδ hl
  have hkdeq : deriv k = oscillatoryKernel σ c :=
    deriv_oscillatoryKernel_eq_signedDerivativeAmplitude σ ha hδ hl
  have hps : ∀ v < 0, p v = 0 :=
    fun _ hv => oscillatoryKernel_eq_zero_of_neg σ hδ hbl hv
  have hks : ∀ v < 0, k v = 0 :=
    fun _ hv => oscillatoryKernel_eq_zero_of_neg σ hδ hl hv
  constructor
  · have h := S.resolventAverage_kill_norm_le r hr hp hps hpi hpdi hdi
    rw [kernelOperator_congr S (hpdi.sub hdi) hk hkeq.symm] at h
    refine h.trans ?_
    calc
      _ ≤ r * (1 + M) * (C * M ^ 3 * ((9 / 2) * A * Real.sqrt (N ^ (4 / 3 : ℝ)))) +
          M * (6 * M * A * (2 * N) ^ (-1 / 4 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hBp (by have := S.bound_nonneg; positivity))
          (mul_le_mul_of_nonneg_left hBd S.bound_nonneg)
      _ = _ := by ring
  · have h := S.resolventAverage_keep_norm_le r hr (k := k) hkdiff hks hk hkdi
    have hdop : S.kernelOperator (deriv k) hkdi = S.kernelOperator (oscillatoryKernel σ c) hci := by
      exact kernelOperator_congr S hkdi hci hkdeq
    rw [hdop] at h
    refine h.trans ((mul_le_mul_of_nonneg_left hBc (div_nonneg S.bound_nonneg hr.le)).trans_eq ?_)
    field_simp

end ProofProject
