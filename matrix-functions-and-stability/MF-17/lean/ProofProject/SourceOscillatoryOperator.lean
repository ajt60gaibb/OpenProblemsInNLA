import ProofProject.FiniteFourierReconstruction
import ProofProject.OscillatoryKernel
import ProofProject.SourceScalarBudget

/-!
# The actual one-interval oscillatory semigroup integral

The finite reconstruction length is selected from the original amplitude's
support. Every integral is a strong vector integral, and the estimates apply
to arbitrary complete complex Hilbert spaces.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

universe u

namespace ProofProject

/-- The bounded upper support determines a finite reconstruction range. This
choice imposes no extra cutoff or approximation on the actual source kernel. -/
theorem sourceOscillatoryKernel_finite_support {N : ℝ} (hN : 0 < N)
    {a : ℝ → ℂ}
    (hlower : ∀ u : ℝ, u < 2 * N → a u = 0)
    (hupper : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
    (σ : ℝ) :
    ∃ n : ℕ, ∀ u : ℝ, u ∉ Icc (2 * N) (((n : ℝ) + 1) * N) →
      oscillatoryKernel σ a u = 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * N ^ (4 / 3 : ℝ) / N)
  have hcover : 4 * N ^ (4 / 3 : ℝ) ≤ ((n : ℝ) + 1) * N := by
    have hh := (div_lt_iff₀ hN).mp hn
    nlinarith
  refine ⟨n, fun u hu => ?_⟩
  rw [oscillatoryKernel_eq_zero_iff]
  by_cases hlo : u < 2 * N
  · exact hlower u hlo
  · have hup : ((n : ℝ) + 1) * N < u := by
      by_contra h
      exact hu ⟨le_of_not_gt hlo, le_of_not_gt h⟩
    exact hupper u (hcover.trans_lt hup)

/-- Compact support of the actual signed oscillatory kernel follows directly
from the two original support thresholds. -/
theorem sourceOscillatoryKernel_hasCompactSupport {N : ℝ} (hN : 0 < N)
    {a : ℝ → ℂ}
    (hlower : ∀ u : ℝ, u < 2 * N → a u = 0)
    (hupper : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
    (σ : ℝ) : HasCompactSupport (oscillatoryKernel σ a) := by
  obtain ⟨n, hsupp⟩ := sourceOscillatoryKernel_finite_support hN hlower hupper σ
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro u hu
  by_contra h
  exact hu (hsupp u h)

namespace BoundedSemigroup

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The actual oscillatory vector integral is integrable before any uniform
Fourier estimate is applied. No separability assumption on `H` is used. -/
theorem sourceOscillatoryOrbit_integrable (S : BoundedSemigroup M H)
    {N : ℝ} (hN : 0 < N) {a : ℝ → ℂ} (ha : Continuous a)
    (hlower : ∀ u : ℝ, u < 2 * N → a u = 0)
    (hupper : ∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0)
    (σ : ℝ) (x : H) :
    Integrable (fun u : ℝ => oscillatoryKernel σ a u • S.op u x) := by
  have hk : Integrable (oscillatoryKernel σ a) :=
    (oscillatoryKernel_continuous σ ha).integrable_of_hasCompactSupport
      (sourceOscillatoryKernel_hasCompactSupport hN hlower hupper σ)
  apply (S.kernelOrbit_integrable hk x).congr
  filter_upwards [] with v
  by_cases hv : 0 ≤ v
  · simp only [positiveOrbit, max_eq_left hv]
  · have hz : oscillatoryKernel σ a v = 0 :=
      oscillatoryKernel_eq_zero_of_neg σ (by positivity : 0 < 2 * N)
        hlower (lt_of_not_ge hv)
    simp only [hz, zero_smul]

end BoundedSemigroup

/-- The one-interval source oscillatory estimate, for either phase sign and
arbitrary complete complex Hilbert spaces in the fixed universe. The absolute
constant precedes every semigroup, amplitude, scale, and vector parameter. -/
theorem exists_sourceOscillatoryOperator_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ℝ) (S : BoundedSemigroup M H) (N A0 : ℝ), 16 ≤ N → 0 ≤ A0 →
      ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u : ℝ, u < 2 * N → a u = 0) →
      (∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0) →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ x : H,
        ‖∫ u : ℝ, oscillatoryKernel σ a u • S.op u x‖ ≤ C * M ^ 3 * A0 * ‖x‖ := by
  obtain ⟨K, hK, hbudget⟩ := exists_sourceScalarBudget_signed
  refine ⟨K, hK, ?_⟩
  intro H _ _ _ M S N A0 hN16 hA0 a ha hlower hupper h0 h1 h2 σ hσ x
  have hN : 0 < N := by linarith
  obtain ⟨n, hsupp⟩ := sourceOscillatoryKernel_finite_support hN hlower hupper σ
  have hkd : ContDiff ℝ ∞ (oscillatoryKernel σ a) :=
    oscillatoryKernel_contDiff σ ha (by positivity : 0 < 2 * N) hlower
  have h := S.norm_sourceKernelIntegral_le N hN n (oscillatoryKernel σ a) hkd hsupp
    (mul_nonneg hK.le hA0)
    (fun ξ => hbudget A0 hA0 a ha h0 h1 h2 N hN hupper σ hσ (Finset.range n) ξ) x
  exact h.trans_eq (by ring)

/-- The same absolute estimate for the bounded operator defined by the strong
kernel integral. The integrability proof supplied to `kernelOperator` is arbitrary. -/
theorem exists_sourceOscillatoryKernelOperator_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ℝ) (S : BoundedSemigroup M H) (N A0 : ℝ), 16 ≤ N → 0 ≤ A0 →
      ∀ a : ℝ → ℂ, ContDiff ℝ ∞ a →
      (∀ u : ℝ, u < 2 * N → a u = 0) →
      (∀ u : ℝ, 4 * N ^ (4 / 3 : ℝ) < u → a u = 0) →
      (∀ u > 0, ‖a u‖ ≤ A0 * u ^ (-3 / 4 : ℝ)) →
      (∀ u > 0, ‖deriv a u‖ ≤ A0 * u ^ (-3 / 4 - 1 : ℝ)) →
      (∀ u > 0, ‖deriv (deriv a) u‖ ≤ A0 * u ^ (-3 / 4 - 2 : ℝ)) →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ∀ hk : Integrable (oscillatoryKernel σ a),
        ‖S.kernelOperator (oscillatoryKernel σ a) hk‖ ≤ C * M ^ 3 * A0 := by
  obtain ⟨C, hC, hbound⟩ := exists_sourceOscillatoryOperator_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro H _ _ _ M S N A0 hN hA0 a ha hlower hupper h0 h1 h2 σ hσ hk
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg hC.le (pow_nonneg S.bound_nonneg _)) hA0)
  intro x
  rw [S.kernelOperator_apply_of_nonneg_support]
  · exact hbound H M S N A0 hN hA0 a ha hlower hupper h0 h1 h2 σ hσ x
  · intro v hv
    exact oscillatoryKernel_eq_zero_of_neg σ (by linarith : 0 < 2 * N) hlower hv

end ProofProject
