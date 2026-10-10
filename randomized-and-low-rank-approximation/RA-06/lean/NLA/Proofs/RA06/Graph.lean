import NLA.Proofs.RA06.Basic

/-! Unordered complete-graph energies used by the RA-06 counterexample. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.RA06

/-- An edge is a strictly ordered pair, representing an unordered pair once. -/
abbrev Edge (v : ℕ) := {ij : Fin v × Fin v // ij.1 < ij.2}

def Incident {v : ℕ} (u : Fin v) (e : Edge v) : Prop :=
  e.1.1 = u ∨ e.1.2 = u

instance instDecidableIncident {v : ℕ} (u : Fin v) (e : Edge v) :
    Decidable (Incident u e) := by
  unfold Incident
  infer_instance

noncomputable def EdgePower {v : ℕ} (p : ℝ)
    (z : Fin v → ℝ) (e : Edge v) : ℝ :=
  Real.rpow |z e.1.1 - z e.1.2| p

noncomputable def CompleteEnergy {v : ℕ} (p : ℝ)
    (z : Fin v → ℝ) : ℝ :=
  ∑ e : Edge v, EdgePower p z e

noncomputable def WeightedEnergy {v : ℕ} (p : ℝ)
    (w : Edge v → ℝ) (z : Fin v → ℝ) : ℝ :=
  ∑ e : Edge v, w e * EdgePower p z e

def SingletonPotential {v : ℕ} (u : Fin v) : Fin v → ℝ :=
  fun j => if j = u then 1 else 0

/-- At a singleton potential an edge contributes one exactly when incident. -/
theorem edgePower_singleton {v : ℕ} (p : ℝ) (hp : 0 < p)
    (u : Fin v) (e : Edge v) :
    EdgePower p (SingletonPotential u) e = if Incident u e then 1 else 0 := by
  have hne : e.1.1 ≠ e.1.2 := ne_of_lt e.2
  by_cases hi : e.1.1 = u
  · have hj : e.1.2 ≠ u := by
      intro h
      exact hne (hi.trans h.symm)
    simp [EdgePower, SingletonPotential, Incident, hi, hj, Real.rpow_eq_pow]
  · by_cases hj : e.1.2 = u
    · simp [EdgePower, SingletonPotential, Incident, hi, hj, Real.rpow_eq_pow]
    · simp [EdgePower, SingletonPotential, Incident, hi, hj,
        Real.rpow_eq_pow, hp.ne']

/-- The original complete-graph energy at a singleton is its ordinary degree. -/
theorem completeEnergy_singleton {v : ℕ} (p : ℝ) (hp : 0 < p)
    (u : Fin v) :
    CompleteEnergy p (SingletonPotential u) =
      ((Finset.univ.filter (Incident u)).card : ℝ) := by
  classical
  simp [CompleteEnergy, edgePower_singleton p hp]

/-- The sampled or otherwise reweighted energy at a singleton is the
weighted degree of that vertex. -/
theorem weightedEnergy_singleton {v : ℕ} (p : ℝ) (hp : 0 < p)
    (w : Edge v → ℝ) (u : Fin v) :
    WeightedEnergy p w (SingletonPotential u) =
      ∑ e ∈ Finset.univ.filter (Incident u), w e := by
  classical
  simp [WeightedEnergy, edgePower_singleton p hp, Finset.sum_ite]

/-- Simultaneous energy preservation controls every weighted vertex degree. -/
theorem weightedDegree_bounds {v : ℕ} (p ε : ℝ) (hp : 0 < p)
    (w : Edge v → ℝ)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    (1 - ε) * ((Finset.univ.filter (Incident u)).card : ℝ) ≤
        ∑ e ∈ Finset.univ.filter (Incident u), w e ∧
      (∑ e ∈ Finset.univ.filter (Incident u), w e) ≤
        (1 + ε) * ((Finset.univ.filter (Incident u)).card : ℝ) := by
  simpa only [completeEnergy_singleton p hp u,
    weightedEnergy_singleton p hp w u] using happrox (SingletonPotential u)

/-- The nonnegative energy of one complete-graph star is bounded by the
energy of the entire graph. -/
theorem starEnergy_le_complete {v : ℕ} (p : ℝ)
    (z : Fin v → ℝ) (u : Fin v) :
    (∑ e ∈ Finset.univ.filter (Incident u), EdgePower p z e) ≤
      CompleteEnergy p z := by
  classical
  unfold CompleteEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact Finset.mem_univ e
  · intro e _ _
    exact Real.rpow_nonneg (abs_nonneg _) _

#print axioms edgePower_singleton
#print axioms completeEnergy_singleton
#print axioms weightedEnergy_singleton
#print axioms weightedDegree_bounds
#print axioms starEnergy_le_complete

end NLA.Proofs.RA06
