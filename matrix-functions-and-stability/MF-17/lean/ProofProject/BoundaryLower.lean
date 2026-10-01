import ProofProject.EndpointDeficit
import ProofProject.ReplicationLower

/-!
# The lower bound from the weighted-polynomial boundary and gain estimates

The boundary and gain estimates imply the lower bound through coefficient
replication. The explicit alternating coefficient vector is used throughout.
-/

noncomputable section

namespace ProofProject

universe u

/-- A source weighted-polynomial model before replication. For positive n,
the alternating vector is automatically a nonzero witness. -/
def HasBoundaryModel (M B : ℝ) (n : ℕ) (gain : ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (f : Fin n → H),
    (∀ i, ‖f i‖ = 1) ∧ HasBoundaryEstimate f M B ∧
    gain ^ 2 * ‖finiteSynthesis f (fun i => (-1 : ℂ) ^ i.val)‖ ^ 2 ≤
      ‖finiteSynthesis f (fun _ => 1)‖ ^ 2

/-- The source's uniform boundary estimate and explicit Dirichlet witness
suffice for the exact finite-dimensional growth lower bound. All intervening
quadratic, replication, generator, and time-transport arguments are proved. -/
theorem finite_dimensional_lower_of_boundary_models {M : ℝ} (hM : 1 < M)
    (hmodels : ∃ B : ℝ, 0 < B ∧ ∃ d : ℝ, 0 < d ∧ ∃ n₀ : ℕ,
      ∀ n : ℕ, n₀ ≤ n →
        HasBoundaryModel.{u} M B n (d * (n : ℝ) ^ growthExponent M)) :
    ∃ d : ℝ, 0 < d ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, t₀ ≤ t →
        HasFiniteWitness.{u} M t (d * growthLog t ^ growthExponent M) := by
  obtain ⟨B, hB, d, hd, n₀, hmodels⟩ := hmodels
  obtain ⟨r, hr, hbudget⟩ := exists_replication_count
    (C := (M ^ 4 + 1) / (M ^ 2 - 1)) (by positivity : 0 < 1 / (4 * B))
  apply finite_dimensional_lower_of_sign_models hM
  refine ⟨r, hr, d, hd, max 1 n₀, ?_⟩
  intro n hn
  obtain ⟨H, hnorm, hip, f, hf, hb, hg⟩ := hmodels n ((le_max_right 1 n₀).trans hn)
  exact hasFiniteSignModel_of_alternating_replication f (by omega) (by omega)
    hM.le hf (HasBoundaryEstimate.replicationDeficits f hM hB hf hb) hbudget hg

end ProofProject
