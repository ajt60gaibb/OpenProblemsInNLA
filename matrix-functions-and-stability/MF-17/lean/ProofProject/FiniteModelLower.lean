import ProofProject.FiniteModelWitness
import ProofProject.SeparationScale
import ProofProject.DiscreteLower

/-!
# The lower bound from finite sign models

Finite sign models yield discrete admissible witnesses with a linear clock
bound, and hence the finite-dimensional lower bound.
-/

noncomputable section

namespace ProofProject

universe u

/-- A unit family, uniformly bounded elementary patterns, and a nonzero vector
on which a prescribed sign change has gain at least `gain`. -/
def HasFiniteSignModel (M : ℝ) (N : ℕ) (gain : ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (f : Fin N → H),
    (∀ j, ‖f j‖ = 1) ∧
    (∀ (c : Fin N → ℂ) (i : Fin N) (z : ℂ), ‖z‖ ≤ 1 →
      ‖finiteSynthesis f (elementaryPattern i z c)‖ ≤ M * ‖finiteSynthesis f c‖) ∧
    ∃ (p : ℕ → Bool) (c : Fin N → ℂ), c ≠ 0 ∧
      gain ^ 2 * ‖finiteSynthesis f c‖ ^ 2 ≤
        ‖finiteSynthesis f ((fun i => if p i.val then (-1 : ℂ) else 1) * c)‖ ^ 2

/-- Every sufficiently separated sign model supplies the lower-bound witness
and the clock estimate needed for transport to arbitrary larger times. -/
theorem finiteSignModel_discrete_witness {M : ℝ} (hM : 1 < M) {r n : ℕ}
    (hr : 1 ≤ r) (hn : 1 ≤ n) {g : ℝ} (hg : 0 ≤ g)
    (hmodel : HasFiniteSignModel.{u} M (r * n) g)
    (hsmall : ((r * n : ℕ) : ℝ) *
      Real.exp (-(metricGamma M (r * n) / (12 * M ^ 2)) * (n : ℝ) ^ 3) ≤
        metricGamma M (r * n) / (12 * M ^ 2)) :
    ∃ t : ℝ, 0 < t ∧ growthLog t ≤ peakClockConstant M r * n ∧
      HasFiniteWitness.{u} M t ((Real.exp (-Real.pi) / Real.sqrt 2) * g - 1) := by
  obtain ⟨H, hnorm, hip, f, hf, hpattern, p, c, hc, hgain⟩ := hmodel
  have hN : 0 < r * n := Nat.mul_pos (by omega) (by omega)
  have hsmall' : ((r * n : ℕ) : ℝ) *
      Real.exp (-(metricGamma M (r * n) / (12 * M ^ 2)) * ((n ^ 3 : ℕ) : ℝ)) ≤
        metricGamma M (r * n) / (12 * M ^ 2) := by
    simpa only [Nat.cast_pow] using hsmall
  have hw := finiteModel_finiteWitness f hM hN hf hpattern p
    (show 1 ≤ n ^ 3 from one_le_pow₀ hn) hsmall' (sq_nonneg g) hc hgain
  have hsqrt : Real.sqrt (g ^ 2 / 2) = g / Real.sqrt 2 := by
    rw [Real.sqrt_div (sq_nonneg g), Real.sqrt_sq hg]
  rw [hsqrt] at hw
  refine ⟨peakTime M (r * n) (separatedInteger (n ^ 3) p (r * n - 1)),
    peakTime_pos (by linarith) hN _, peakTime_clock_linear (by linarith) hr hn p, ?_⟩
  convert hw using 1 <;> ring

open Filter in
/-- The scalar smallness assumption disappears eventually for a fixed replication
number. This theorem still assumes existence of the finite sign models. -/
theorem finiteSignModels_eventually_witness {M d α : ℝ} (hM : 1 < M)
    (hd : 0 < d) {r : ℕ} (hr : 1 ≤ r) {n₀ : ℕ}
    (hmodels : ∀ n : ℕ, n₀ ≤ n →
      HasFiniteSignModel.{u} M (r * n) (d * (n : ℝ) ^ α)) :
    ∀ᶠ n : ℕ in atTop, ∃ t : ℝ, 0 < t ∧
      growthLog t ≤ peakClockConstant M r * n ∧
      HasFiniteWitness.{u} M t
        ((Real.exp (-Real.pi) / Real.sqrt 2 * d) * (n : ℝ) ^ α - 1) := by
  filter_upwards [eventually_separation_smallness hM (by omega : 0 < r),
    eventually_ge_atTop n₀] with n hn hn₀
  obtain ⟨t, ht, hclock, hw⟩ := finiteSignModel_discrete_witness hM hr hn.1
    (mul_nonneg hd.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hmodels n hn₀) hn.2
  exact ⟨t, ht, hclock, by simpa only [mul_assoc] using hw⟩

/-- The finite-model premise alone suffices for the lower-bound conclusion;
all generator, separation, metric, and time-transport obligations are proved. -/
theorem finiteWitness_lower_of_signModels {M d α : ℝ} (hM : 1 < M)
    (hα : 0 < α) (hd : 0 < d) {r : ℕ} (hr : 1 ≤ r) (n₀ : ℕ)
    (hmodels : ∀ n : ℕ, n₀ ≤ n →
      HasFiniteSignModel.{u} M (r * n) (d * (n : ℝ) ^ α)) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t → HasFiniteWitness.{u} M t (c * growthLog t ^ α) := by
  obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp
    (finiteSignModels_eventually_witness hM hd hr hmodels)
  exact finiteWitness_lower_of_discrete (by linarith) hα
    (by positivity : 0 < Real.exp (-Real.pi) / Real.sqrt 2 * d)
    (peakClockConstant_pos (by linarith) r) n₁ hn₁

/-- Specialization to the sharp exponent, assuming the displayed finite sign models. -/
theorem finite_dimensional_lower_of_sign_models {M : ℝ} (hM : 1 < M)
    (hmodels : ∃ r : ℕ, 1 ≤ r ∧ ∃ d : ℝ, 0 < d ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        HasFiniteSignModel.{u} M (r * n) (d * (n : ℝ) ^ growthExponent M)) :
    ∃ c : ℝ, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (c * growthLog t ^ growthExponent M) := by
  obtain ⟨r, hr, d, hd, n₀, hmodels⟩ := hmodels
  exact finiteWitness_lower_of_signModels hM (growthExponent_pos hM) hd hr n₀ hmodels

end ProofProject
