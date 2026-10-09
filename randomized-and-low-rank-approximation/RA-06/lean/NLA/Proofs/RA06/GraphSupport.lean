import NLA.Proofs.RA06.GraphPower

/-! Support-neighbor bookkeeping for the complete-graph witness. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

/-- A distinct vertex connected to `u` by a positive-weight edge. -/
def SupportedNeighbor {v : ℕ} (w : Edge v → ℝ)
    (u j : Fin v) : Prop :=
  j ≠ u ∧ ∃ e : Edge v, Incident u e ∧ Incident j e ∧ 0 < w e

noncomputable def SupportNeighbors {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) : Finset (Fin v) := by
  classical
  exact Finset.univ.filter (SupportedNeighbor w u)

noncomputable def SupportDegree {v : ℕ} (w : Edge v → ℝ) (u : Fin v) : ℕ :=
  (SupportNeighbors w u).card

noncomputable def OutsideNeighbors {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) : Finset (Fin v) :=
  (Finset.univ.erase u) \ SupportNeighbors w u

noncomputable def WitnessPotential {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) (t : ℝ) : Fin v → ℝ := by
  classical
  exact fun j => if j = u then 1 else if j ∈ SupportNeighbors w u then t else 0

theorem witness_at_center {v : ℕ} (w : Edge v → ℝ)
    (u : Fin v) (t : ℝ) : WitnessPotential w u t u = 1 := by
  classical
  simp [WitnessPotential]

theorem witness_at_neighbor {v : ℕ} (w : Edge v → ℝ)
    (u j : Fin v) (t : ℝ) (hj : j ∈ SupportNeighbors w u) :
    WitnessPotential w u t j = t := by
  classical
  have hju : j ≠ u := by
    change j ∈ Finset.univ.filter (SupportedNeighbor w u) at hj
    exact (Finset.mem_filter.mp hj).2.1
  simp [WitnessPotential, hju, hj]

theorem witness_at_outside {v : ℕ} (w : Edge v → ℝ)
    (u j : Fin v) (t : ℝ) (hju : j ≠ u)
    (hj : j ∉ SupportNeighbors w u) :
    WitnessPotential w u t j = 0 := by
  classical
  simp [WitnessPotential, hju, hj]

/-- A support degree cannot exceed the ordinary complete-graph degree. -/
theorem supportDegree_le {v : ℕ} (w : Edge v → ℝ) (u : Fin v) :
    SupportDegree w u ≤ v - 1 := by
  classical
  have hsubset : SupportNeighbors w u ⊆ Finset.univ.erase u := by
    intro j hj
    have hju : j ≠ u := by
      change j ∈ Finset.univ.filter (SupportedNeighbor w u) at hj
      exact (Finset.mem_filter.mp hj).2.1
    simp [hju]
  have hcard := Finset.card_le_card hsubset
  simpa [SupportDegree] using hcard

theorem outside_card {v : ℕ} (w : Edge v → ℝ) (u : Fin v) :
    (OutsideNeighbors w u).card = (v - 1) - SupportDegree w u := by
  classical
  have hsubset : SupportNeighbors w u ⊆ Finset.univ.erase u := by
    intro j hj
    change j ∈ Finset.univ.filter (SupportedNeighbor w u) at hj
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp hj).2.1, Finset.mem_univ _⟩
  simp [OutsideNeighbors, SupportDegree, Finset.card_sdiff,
    Finset.inter_eq_left.mpr hsubset]

/-- An embedding has at least one supported neighbor at every vertex. -/
theorem supportDegree_pos {v : ℕ}
    (p ε : ℝ) (hp : 0 < p) (hε : ε < 1)
    (hv : 1 < v) (w : Edge v → ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    0 < SupportDegree w u := by
  classical
  obtain ⟨e, he, hwe⟩ := positive_support_edge p ε hp hε hv w hw happrox u
  apply Finset.card_pos.mpr
  rcases he with hu | hu
  · let j := e.val.2
    have hne : j ≠ u := by
      intro hj
      exact (ne_of_lt e.property) (hu.trans hj.symm)
    refine ⟨j, ?_⟩
    change j ∈ Finset.univ.filter (SupportedNeighbor w u)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨hne, e, Or.inl hu, Or.inr rfl, hwe⟩⟩
  · let j := e.val.1
    have hne : j ≠ u := by
      intro hj
      exact (ne_of_lt e.property) (hj.trans hu.symm)
    refine ⟨j, ?_⟩
    change j ∈ Finset.univ.filter (SupportedNeighbor w u)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨hne, e, Or.inr hu, Or.inl rfl, hwe⟩⟩

#print axioms supportDegree_le
#print axioms outside_card
#print axioms supportDegree_pos
#print axioms witness_at_center
#print axioms witness_at_neighbor
#print axioms witness_at_outside

end NLA.Proofs.RA06
