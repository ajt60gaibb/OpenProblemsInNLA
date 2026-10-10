import NLA.Proofs.RA06.GraphSampling
import NLA.Proofs.RA06.GraphSupport
import NLA.Proofs.RA06.Bernoulli

/-! Exact support count for the sampled graph. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

open NLA.Statements.RA06

theorem graphMatrix_rows_pos (d : ℕ) (hd : 0 < d) :
    0 < Fintype.card (Edge (d + 1)) := by
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨(0, Fin.succ (⟨0, hd⟩ : Fin d)), by
    change (0 : ℕ) < 1
    omega⟩⟩

theorem sampleWeight_positive_iff (d : ℕ) (hd : 0 < d)
    (p α : ℝ) (hα : 0 < α)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool)
    (e : Edge (d + 1)) :
    0 < SampleWeight d p α kept e ↔
      kept ((edgeIndex d).symm e) = true := by
  classical
  have hq : 0 < RetentionProbability (GraphMatrix d) p α
      ((edgeIndex d).symm e) :=
    retentionProbability_pos (GraphMatrix d) p α
      (graphMatrix_fullColumnRank d) (graphMatrix_rows_pos d hd) hd hα _
  by_cases h : kept ((edgeIndex d).symm e) = true
  · simpa [SampleWeight, h] using (one_div_pos.mpr hq)
  · simp [SampleWeight, h]

noncomputable def PositiveEdgeCount {v : ℕ} (w : Edge v → ℝ) : ℕ :=
  (Finset.univ.filter (fun e => 0 < w e)).card

noncomputable def PositiveIncidentCount {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) : ℕ :=
  (Finset.univ.filter (fun e => Incident u e ∧ 0 < w e)).card

private theorem incident_vertices_card_two {v : ℕ} (e : Edge v) :
    (Finset.univ.filter (fun u : Fin v => Incident u e)).card = 2 := by
  classical
  have hset : Finset.univ.filter (fun u : Fin v => Incident u e) =
      {e.val.1, e.val.2} := by
    ext u
    simp [Incident, eq_comm]
  rw [hset]
  simp [ne_of_lt e.property]

/-- The usual handshake identity, stated directly for the positive edges of
the ordered-pair graph model. -/
theorem sum_positiveIncidentCount_eq_two_edges {v : ℕ}
    (w : Edge v → ℝ) :
    (∑ u : Fin v, PositiveIncidentCount w u) =
      2 * PositiveEdgeCount w := by
  classical
  simp only [PositiveIncidentCount, PositiveEdgeCount]
  calc
    (∑ u : Fin v,
      (Finset.univ.filter (fun e : Edge v => Incident u e ∧ 0 < w e)).card) =
        ∑ u : Fin v, ∑ e : Edge v,
          if Incident u e ∧ 0 < w e then (1 : ℕ) else 0 := by simp
    _ = ∑ e : Edge v, ∑ u : Fin v,
          if Incident u e ∧ 0 < w e then (1 : ℕ) else 0 := Finset.sum_comm
    _ = ∑ e : Edge v, if 0 < w e then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases he : 0 < w e
      · simp only [he, and_true, if_true]
        simpa only [← Finset.card_filter] using incident_vertices_card_two e
      · simp [he]
    _ = 2 * (Finset.univ.filter (fun e : Edge v => 0 < w e)).card := by
      simp [Finset.sum_ite, mul_comm]

private theorem otherEndpoint_eq_of_two_incident {v : ℕ}
    (u j : Fin v) (e : Edge v)
    (hu : Incident u e) (hj : Incident j e) (hju : j ≠ u) :
    (otherEndpoint u ⟨e, hu⟩).val = j := by
  rcases hu with hu | hu
  · rcases hj with hj | hj
    · exact False.elim (hju (hj.symm.trans hu))
    · simp [otherEndpoint, hu, hj]
  · rcases hj with hj | hj
    · simp [otherEndpoint, hj, hju]
    · exact False.elim (hju (hj.symm.trans hu))

private theorem incident_other_of_edgeOfOther {v : ℕ}
    (u : Fin v) (j : OtherVertex u) :
    Incident j.val (edgeOfOther u j).val := by
  by_cases h : u < j.val
  · simp [edgeOfOther, h, Incident]
  · simp [edgeOfOther, h, Incident]

/-- A supported neighbor is exactly a positive edge from the center, using
the canonical edge associated with that neighbor. -/
theorem supportedNeighbor_iff_edgePositive {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) (j : OtherVertex u) :
    SupportedNeighbor w u j.val ↔ 0 < w (edgeOfOther u j).val := by
  constructor
  · intro hj
    obtain ⟨_, e, hu, hje, hwe⟩ := hj
    let ee : IncidentEdge u := ⟨e, hu⟩
    have hother : otherEndpoint u ee = j := by
      apply Subtype.ext
      exact otherEndpoint_eq_of_two_incident u j.val e hu hje j.property
    have hback := (incidentEdgeEquivOther u).left_inv ee
    change edgeOfOther u (otherEndpoint u ee) = ee at hback
    rw [hother] at hback
    have heq : (edgeOfOther u j).val = e := congrArg Subtype.val hback
    simpa only [heq] using hwe
  · intro hwe
    exact ⟨j.property, (edgeOfOther u j).val,
      (edgeOfOther u j).property, incident_other_of_edgeOfOther u j, hwe⟩

theorem supportDegree_eq_positiveIncidentCount {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) :
    SupportDegree w u = PositiveIncidentCount w u := by
  classical
  unfold SupportDegree PositiveIncidentCount
  apply Finset.card_bij
    (fun j (hj : j ∈ SupportNeighbors w u) =>
      (edgeOfOther u ⟨j, (Finset.mem_filter.mp hj).2.1⟩).val)
  · intro j hj
    have hsup : SupportedNeighbor w u j := (Finset.mem_filter.mp hj).2
    let jo : OtherVertex u := ⟨j, hsup.1⟩
    have hpos := (supportedNeighbor_iff_edgePositive w u jo).mp hsup
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (edgeOfOther u jo).property, hpos⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    let a : OtherVertex u := ⟨j₁, (Finset.mem_filter.mp hj₁).2.1⟩
    let b : OtherVertex u := ⟨j₂, (Finset.mem_filter.mp hj₂).2.1⟩
    have heq' : edgeOfOther u a = edgeOfOther u b := Subtype.ext heq
    have hother := congrArg (otherEndpoint u) heq'
    have ha : otherEndpoint u (edgeOfOther u a) = a :=
      (incidentEdgeEquivOther u).right_inv a
    have hb : otherEndpoint u (edgeOfOther u b) = b :=
      (incidentEdgeEquivOther u).right_inv b
    rw [ha, hb] at hother
    exact congrArg Subtype.val hother
  · intro e he
    have hu : Incident u e := (Finset.mem_filter.mp he).2.1
    have hwe : 0 < w e := (Finset.mem_filter.mp he).2.2
    let ee : IncidentEdge u := ⟨e, hu⟩
    let jo : OtherVertex u := otherEndpoint u ee
    have hback : edgeOfOther u jo = ee := (incidentEdgeEquivOther u).left_inv ee
    have hpos : 0 < w (edgeOfOther u jo).val := by
      simpa only [hback] using hwe
    have hsup : SupportedNeighbor w u jo.val :=
      (supportedNeighbor_iff_edgePositive w u jo).mpr hpos
    have hjmem : jo.val ∈ SupportNeighbors w u :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsup⟩
    refine ⟨jo.val, hjmem, ?_⟩
    exact congrArg Subtype.val hback

theorem sum_supportDegree_eq_two_edges {v : ℕ}
    (w : Edge v → ℝ) :
    (∑ u : Fin v, SupportDegree w u) =
      2 * PositiveEdgeCount w := by
  simp_rw [supportDegree_eq_positiveIncidentCount]
  exact sum_positiveIncidentCount_eq_two_edges w

theorem positiveEdgeCount_lower_of_all_degrees {v : ℕ}
    (w : Edge v → ℝ) (T : ℝ)
    (hdegree : ∀ u : Fin v, T ≤ (SupportDegree w u : ℝ)) :
    (v : ℝ) * T ≤ 2 * (PositiveEdgeCount w : ℝ) := by
  have hsum : (∑ _u : Fin v, T) ≤
      ∑ u : Fin v, (SupportDegree w u : ℝ) := by
    apply Finset.sum_le_sum
    intro u _
    exact hdegree u
  have hhand := sum_supportDegree_eq_two_edges w
  exact calc
    (v : ℝ) * T = ∑ _u : Fin v, T := by simp
    _ ≤ ∑ u : Fin v, (SupportDegree w u : ℝ) := hsum
    _ = 2 * (PositiveEdgeCount w : ℝ) := by exact_mod_cast hhand

/-- An edge has positive sample weight exactly when its corresponding row
was retained. Thus graph support count equals the realized sample size. -/
theorem sample_positiveEdgeCount_eq_retainedCount
    (d : ℕ) (hd : 0 < d) (p α : ℝ) (hα : 0 < α)
    (kept : Fin (Fintype.card (Edge (d + 1))) → Bool) :
    PositiveEdgeCount (SampleWeight d p α kept) = RetainedCount kept := by
  classical
  unfold PositiveEdgeCount RetainedCount
  apply Finset.card_equiv (edgeIndex d).symm
  intro e
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact sampleWeight_positive_iff d hd p α hα kept e

#print axioms graphMatrix_rows_pos
#print axioms sampleWeight_positive_iff
#print axioms sample_positiveEdgeCount_eq_retainedCount
#print axioms sum_positiveIncidentCount_eq_two_edges
#print axioms supportedNeighbor_iff_edgePositive
#print axioms supportDegree_eq_positiveIncidentCount
#print axioms sum_supportDegree_eq_two_edges
#print axioms positiveEdgeCount_lower_of_all_degrees

end NLA.Proofs.RA06
