import ProofProject.ReplicationModels

/-!
# Uniform replication and the lower-bound reduction

The original families may vary with dimension. Only the two deficit constants
must be uniform, so one replication count works for the entire sequence.
-/

noncomputable section

namespace ProofProject

universe u

/-- An original-space model: a unit family with uniform endpoint
and interior deficit constants and an explicit nonzero sign-gain vector. -/
def HasDeficitSignModel (M c C : ℝ) (n : ℕ) (gain : ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (f : Fin n → H),
    (∀ i, ‖f i‖ = 1) ∧ HasReplicationDeficits f M c C ∧
    ∃ (p : Fin n → Bool) (a : Fin n → ℂ), a ≠ 0 ∧
      gain ^ 2 * ‖finiteSynthesis f a‖ ^ 2 ≤
        ‖finiteSynthesis f ((fun i => if p i then (-1 : ℂ) else 1) * a)‖ ^ 2

/-- A single replication count works for every dimension and gain once the
original-space deficit constants are fixed. -/
theorem exists_uniform_replication {M c C : ℝ} (hM : 1 ≤ M) (hc : 0 < c) :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ (n : ℕ) (g : ℝ),
      HasDeficitSignModel.{u} M c C n g → HasFiniteSignModel.{u} M (r * n) g := by
  obtain ⟨r, hr, hbudget⟩ := exists_replication_count (C := C) hc
  refine ⟨r, hr, ?_⟩
  intro n g hm
  obtain ⟨H, hnorm, hip, f, hf, hdef, p, a, ha, hgain⟩ := hm
  exact hasFiniteSignModel_of_replication f (by omega) hM hf hdef hbudget p a ha hgain

/-- The analytic construction need only supply original-space deficits and a
sign-gain vector. Replication and the entire stable-generator construction
then imply the lower bound at the exact exponent. -/
theorem finite_dimensional_lower_of_deficit_models {M : ℝ} (hM : 1 < M)
    (hmodels : ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, ∃ d : ℝ, 0 < d ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        HasDeficitSignModel.{u} M c C n (d * (n : ℝ) ^ growthExponent M)) :
    ∃ d : ℝ, 0 < d ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (d * growthLog t ^ growthExponent M) := by
  obtain ⟨c, hc, C, d, hd, n₀, hmodels⟩ := hmodels
  obtain ⟨r, hr, hrep⟩ := exists_uniform_replication (M := M) (C := C) hM.le hc
  apply finite_dimensional_lower_of_sign_models hM
  exact ⟨r, hr, d, hd, n₀, fun n hn => hrep n _ (hmodels n hn)⟩

end ProofProject
