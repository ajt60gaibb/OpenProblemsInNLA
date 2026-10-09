import ProofProject.SourcePieceAmplitude
import ProofProject.SourceOscillatoryOperator
import ProofProject.ResolventOperatorIdentity

/-!
# The source's actual time-dependent oscillatory pieces

Both signs are realized as bounded operators by strong integration. The
original amplitude bounds are discharged for these particular kernels, giving
the exponential piece estimate with a constant independent of piece and time.
-/

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace ProofProject

def sourcePieceKernel (q : ℕ) (t σ : ℝ) : ℝ → ℂ :=
  oscillatoryKernel σ (sourcePieceAmplitude q t)

theorem sourcePieceKernel_contDiff (q : ℕ) (t σ : ℝ) :
    ContDiff ℝ ∞ (sourcePieceKernel q t σ) :=
  oscillatoryKernel_contDiff σ (sourcePieceAmplitude_contDiff q t)
    (show 0 < 2 * sourcePieceScale q by have := sourcePieceScale_pos q; positivity)
    (fun _ hu => sourcePieceAmplitude_eq_zero_of_le q t hu.le)

theorem sourcePieceKernel_hasCompactSupport (q : ℕ) (t σ : ℝ) :
    HasCompactSupport (sourcePieceKernel q t σ) :=
  oscillatoryKernel_hasCompactSupport σ (sourcePieceAmplitude_hasCompactSupport q t)

theorem sourcePieceKernel_integrable (q : ℕ) (t σ : ℝ) :
    Integrable (sourcePieceKernel q t σ) :=
  (sourcePieceKernel_contDiff q t σ).continuous.integrable_of_hasCompactSupport
    (sourcePieceKernel_hasCompactSupport q t σ)

theorem sourcePieceKernel_eq_zero_of_nonpos (q : ℕ) (t σ : ℝ) {u : ℝ}
    (hu : u ≤ 0) : sourcePieceKernel q t σ u = 0 := by
  apply (oscillatoryKernel_eq_zero_iff σ _ u).mpr
  exact sourcePieceAmplitude_eq_zero_of_le q t
    (hu.trans (by have := sourcePieceScale_pos q; positivity))

/-- The actual signed kernels retain the source's exact finite telescoping. -/
theorem sum_sourcePieceKernel (n : ℕ) (t σ u : ℝ) :
    (∑ q ∈ Finset.range n, sourcePieceKernel q t σ u) =
      ((dampedPower (-3 / 4) t u : ℝ) : ℂ) *
        ((sourcePieceChi (u / (2 * sourcePieceScale n)) -
          sourcePieceChi (u / 32) : ℝ) : ℂ) *
        Complex.exp (((σ * 2 * Real.sqrt u : ℝ) : ℂ) * Complex.I) := by
  simp only [sourcePieceKernel, oscillatoryKernel, sourcePieceAmplitude,
    sourcePieceAmplitudeReal, Complex.ofReal_mul]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← Complex.ofReal_sum,
    sum_sourcePieceCutoff]

namespace BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The source operator `B_q^σ`, with its actual time-dependent amplitude. -/
def sourcePieceOperator (S : BoundedSemigroup M H) (q : ℕ) (t σ : ℝ) : H →L[ℂ] H :=
  S.kernelOperator (sourcePieceKernel q t σ) (sourcePieceKernel_integrable q t σ)

theorem sourcePieceOperator_apply (S : BoundedSemigroup M H)
    (q : ℕ) (t σ : ℝ) (x : H) :
    S.sourcePieceOperator q t σ x =
      ∫ s : ℝ, sourcePieceKernel q t σ s • S.op s x :=
  S.kernelOperator_apply_of_nonneg_support _ _
    (fun _ hs => sourcePieceKernel_eq_zero_of_nonpos q t σ hs.le) x

/-- This is exactly the positive-time source integral. -/
theorem sourcePieceOperator_apply_Ioi (S : BoundedSemigroup M H)
    (q : ℕ) (t σ : ℝ) (x : H) :
    S.sourcePieceOperator q t σ x =
      ∫ s : ℝ in Ioi 0, sourcePieceKernel q t σ s • S.op s x := by
  rw [sourcePieceOperator_apply, ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    dsimp only
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), sourcePieceKernel_eq_zero_of_nonpos q t σ
        (le_of_not_gt hs), zero_smul]

theorem sourcePieceOperator_orbit_integrable (S : BoundedSemigroup M H)
    (q : ℕ) (t σ : ℝ) (x : H) :
    Integrable (fun s : ℝ => sourcePieceKernel q t σ s • S.op s x) := by
  apply (S.kernelOrbit_integrable (sourcePieceKernel_integrable q t σ) x).congr
  filter_upwards [] with s
  by_cases hs : 0 ≤ s
  · simp only [positiveOrbit, max_eq_left hs]
  · simp only [sourcePieceKernel_eq_zero_of_nonpos q t σ (le_of_not_ge hs), zero_smul]

theorem sourcePieceOperator_commutes (S : BoundedSemigroup M H)
    (q : ℕ) (t σ : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    Commute (S.op a) (S.sourcePieceOperator q t σ) :=
  S.kernelOperator_commutes _ _ ha

theorem resolventAverage_sourcePieceOperator_commute (S : BoundedSemigroup M H)
    (r : ℝ) (hr : 0 < r) (q : ℕ) (t σ : ℝ) :
    Commute (S.resolventAverage r hr) (S.sourcePieceOperator q t σ) :=
  S.resolventAverage_kernelOperator_commute r hr (sourcePieceKernel_integrable q t σ)

end BoundedSemigroup

universe u

/-- The source piece estimate, with one absolute constant before every Hilbert
space, semigroup, piece index, positive time and choice of sign. -/
theorem exists_sourcePieceOperator_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (M : ℝ) (S : BoundedSemigroup M H) (q : ℕ) (t : ℝ), 0 < t →
      ∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
        ‖S.sourcePieceOperator q t σ‖ ≤ C * M ^ 3 * Real.exp (-sourcePieceScale q / t) := by
  obtain ⟨K, hK, hbound⟩ := exists_sourceOscillatoryKernelOperator_bound.{u}
  obtain ⟨A, hA, ha⟩ := exists_sourcePieceAmplitude_weighted_bounds_through_three
  refine ⟨K * A, mul_pos hK hA, ?_⟩
  intro H _ _ _ M S q t ht σ hσ
  obtain ⟨h0, h1, h2, _h3⟩ := ha q t ht
  have hup : ∀ v : ℝ, 4 * sourcePieceScale q ^ (4 / 3 : ℝ) < v →
      sourcePieceAmplitude q t v = 0 := by
    intro v hv
    apply sourcePieceAmplitude_eq_zero_of_ge q t
    simpa only [sourcePieceScale_succ] using hv.le
  have h := hbound H M S (sourcePieceScale q) (A * Real.exp (-sourcePieceScale q / t))
    (sourcePieceScale_ge_sixteen q) (by positivity) (sourcePieceAmplitude q t)
    (sourcePieceAmplitude_contDiff q t)
    (fun _ hv => sourcePieceAmplitude_eq_zero_of_le q t hv.le) hup
    h0 h1 h2 σ hσ (sourcePieceKernel_integrable q t σ)
  exact h.trans_eq (by ring)

end ProofProject
