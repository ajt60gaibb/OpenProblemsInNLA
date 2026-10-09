import NLA.Proofs.RA06.Graph

/-! Elementary complete-graph edge counts for RA-06. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

abbrev IncidentEdge {v : ℕ} (u : Fin v) := {e : Edge v // Incident u e}
abbrev OtherVertex {v : ℕ} (u : Fin v) := {j : Fin v // j ≠ u}

def otherEndpoint {v : ℕ} (u : Fin v) (e : IncidentEdge u) : OtherVertex u := by
  let a := e.val.val.1
  let b := e.val.val.2
  by_cases h : a = u
  · refine ⟨b, ?_⟩
    intro hb
    exact (ne_of_lt e.val.property) (h.trans hb.symm)
  · exact ⟨a, h⟩

def edgeOfOther {v : ℕ} (u : Fin v) (j : OtherVertex u) : IncidentEdge u := by
  by_cases h : u < j.val
  · exact ⟨⟨(u, j.val), h⟩, Or.inl rfl⟩
  · have hju : j.val < u := lt_of_le_of_ne (le_of_not_gt h) j.property
    exact ⟨⟨(j.val, u), hju⟩, Or.inr rfl⟩

def incidentEdgeEquivOther {v : ℕ} (u : Fin v) :
    IncidentEdge u ≃ OtherVertex u where
  toFun := otherEndpoint u
  invFun := edgeOfOther u
  left_inv := by
    intro e
    apply Subtype.ext
    apply Subtype.ext
    have he : e.val.val.1 < e.val.val.2 := e.val.property
    rcases e.property with hu | hu
    · have hup : u < e.val.val.2 := by simpa only [← hu] using he
      have hpair : (u, e.val.val.2) = e.val.val := by
        apply Prod.ext
        · exact hu.symm
        · rfl
      simpa [otherEndpoint, edgeOfOther, hu, hup] using hpair
    · have hnot : ¬u < e.val.val.1 := by
        intro hlt
        have hrev : e.val.val.2 < e.val.val.1 := by
          calc
            e.val.val.2 = u := hu
            _ < e.val.val.1 := hlt
        exact (not_lt_of_ge he.le) hrev
      have hfirstNe : e.val.val.1 ≠ u := by
        intro heq
        exact (ne_of_lt he) (heq.trans hu.symm)
      have hpair : (e.val.val.1, u) = e.val.val := by
        apply Prod.ext
        · rfl
        · exact hu.symm
      simpa [otherEndpoint, edgeOfOther, hnot, hfirstNe] using hpair
  right_inv := by
    intro j
    apply Subtype.ext
    by_cases h : u < j.val
    · simp [otherEndpoint, edgeOfOther, h]
    · have hju : j.val < u := lt_of_le_of_ne (le_of_not_gt h) j.property
      simp [otherEndpoint, edgeOfOther, h, j.property]

theorem edgePower_incident_eq {v : ℕ} (p : ℝ)
    (z : Fin v → ℝ) (u : Fin v) (e : IncidentEdge u) :
    EdgePower p z e.val =
      Real.rpow |z u - z (otherEndpoint u e).val| p := by
  rcases e.property with hu | hu
  · simp [EdgePower, otherEndpoint, hu]
  · have hfirstNe : e.val.val.1 ≠ u := by
      intro h
      exact (ne_of_lt e.val.property) (h.trans hu.symm)
    simp [EdgePower, otherEndpoint, hfirstNe, hu, abs_sub_comm]

theorem starEnergy_eq_sum_other {v : ℕ} (p : ℝ)
    (z : Fin v → ℝ) (u : Fin v) :
    (∑ e ∈ Finset.univ.filter (Incident u), EdgePower p z e) =
      ∑ j : OtherVertex u, Real.rpow |z u - z j.val| p := by
  classical
  calc
    (∑ e ∈ Finset.univ.filter (Incident u), EdgePower p z e) =
        ∑ e ∈ Finset.subtype (Incident u) (Finset.univ : Finset (Edge v)),
          EdgePower p z e.val :=
      (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := Incident u) (f := EdgePower p z)).symm
    _ =
        ∑ e : IncidentEdge u, EdgePower p z e.val := by
      simp
    _ = ∑ j : OtherVertex u, Real.rpow |z u - z j.val| p :=
      Fintype.sum_equiv (incidentEdgeEquivOther u)
        (fun e => EdgePower p z e.val)
        (fun j => Real.rpow |z u - z j.val| p)
        (fun e => edgePower_incident_eq p z u e)

/-- Summing the pth powers of all differences from one vertex never exceeds
the complete graph energy; the self-difference is zero for `p>0`. -/
theorem sum_differences_le_complete {v : ℕ} (p : ℝ) (hp : 0 < p)
    (z : Fin v → ℝ) (u : Fin v) :
    (∑ j : Fin v, Real.rpow |z u - z j| p) ≤ CompleteEnergy p z := by
  classical
  have hzero : Real.rpow |z u - z u| p = 0 := by
    simp [Real.rpow_eq_pow, hp.ne']
  have hstar := starEnergy_le_complete p z u
  rw [starEnergy_eq_sum_other] at hstar
  have hsum : (∑ j : Fin v, Real.rpow |z u - z j| p) =
      ∑ j : OtherVertex u, Real.rpow |z u - z j.val| p := by
    calc
      (∑ j : Fin v, Real.rpow |z u - z j| p) =
          ∑ j ∈ Finset.univ.erase u, Real.rpow |z u - z j| p := by
        exact (Finset.sum_erase (Finset.univ : Finset (Fin v))
          (f := fun j => Real.rpow |z u - z j| p) (a := u) hzero).symm
      _ = ∑ j ∈ Finset.univ.filter (fun j : Fin v => j ≠ u),
          Real.rpow |z u - z j| p := by rw [Finset.filter_ne']
      _ = ∑ j ∈ Finset.subtype (fun j : Fin v => j ≠ u) Finset.univ,
          Real.rpow |z u - z j.val| p :=
        (Finset.sum_subtype_eq_sum_filter
          (s := Finset.univ) (p := fun j : Fin v => j ≠ u)
          (f := fun j => Real.rpow |z u - z j| p)).symm
      _ = ∑ j : OtherVertex u, Real.rpow |z u - z j.val| p := by simp
  exact hsum ▸ hstar

/-- Every vertex of `K_v` has exactly `v−1` incident edges. -/
theorem incident_card {v : ℕ} (u : Fin v) :
    (Finset.univ.filter (Incident u)).card = v - 1 := by
  classical
  calc
    (Finset.univ.filter (Incident u)).card = Fintype.card (IncidentEdge u) := by
      simpa using (Finset.card_subtype (Incident u) Finset.univ).symm
    _ = Fintype.card (OtherVertex u) := Fintype.card_congr (incidentEdgeEquivOther u)
    _ = v - 1 := by simp [OtherVertex]

theorem completeEnergy_singleton_exact {v : ℕ}
    (p : ℝ) (hp : 0 < p) (u : Fin v) :
    CompleteEnergy p (SingletonPotential u) = (v - 1 : ℕ) := by
  rw [completeEnergy_singleton p hp u, incident_card]

theorem weightedDegree_bounds_exact {v : ℕ}
    (p ε : ℝ) (hp : 0 < p) (w : Edge v → ℝ)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    (1 - ε) * (v - 1 : ℕ) ≤
        ∑ e ∈ Finset.univ.filter (Incident u), w e ∧
      (∑ e ∈ Finset.univ.filter (Incident u), w e) ≤
        (1 + ε) * (v - 1 : ℕ) := by
  simpa only [incident_card] using weightedDegree_bounds p ε hp w happrox u

/-- Every vertex must have a positive-weight incident edge when the
two-sided embedding preserves its singleton test. -/
theorem positive_support_edge {v : ℕ}
    (p ε : ℝ) (hp : 0 < p) (hε : ε < 1)
    (hv : 1 < v) (w : Edge v → ℝ)
    (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    ∃ e : Edge v, Incident u e ∧ 0 < w e := by
  classical
  have hdegree := (weightedDegree_bounds_exact p ε hp w happrox u).1
  have hcard : 0 < ((v - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hv)
  have hsum : 0 < ∑ e ∈ Finset.univ.filter (Incident u), w e :=
    lt_of_lt_of_le (mul_pos (by linarith) hcard) hdegree
  obtain ⟨e, he, hwe⟩ :=
    (Finset.sum_pos_iff_of_nonneg (fun e _ => hw e)).mp hsum
  exact ⟨e, (Finset.mem_filter.mp he).2, hwe⟩

#print axioms incident_card
#print axioms edgePower_incident_eq
#print axioms starEnergy_eq_sum_other
#print axioms sum_differences_le_complete
#print axioms completeEnergy_singleton_exact
#print axioms weightedDegree_bounds_exact
#print axioms positive_support_edge

end NLA.Proofs.RA06
