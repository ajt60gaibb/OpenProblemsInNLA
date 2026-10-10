import NLA.Proofs.RA06.GraphSupportCount

/-! Finite crossing-edge bookkeeping for the RA-06 support witness. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RA06

abbrev CrossPair {v : ℕ} (W O : Finset (Fin v)) :=
  {a : Fin v // a ∈ W} × {b : Fin v // b ∈ O}

def edgeOfCross {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) (ab : CrossPair W O) : Edge v := by
  have hne : ab.1.val ≠ ab.2.val := by
    intro h
    exact Finset.disjoint_left.mp hdisj ab.1.property (h ▸ ab.2.property)
  by_cases h : ab.1.val < ab.2.val
  · exact ⟨(ab.1.val, ab.2.val), h⟩
  · have hrev : ab.2.val < ab.1.val := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    exact ⟨(ab.2.val, ab.1.val), hrev⟩

theorem edgeOfCross_incident {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) (ab : CrossPair W O) :
    Incident ab.1.val (edgeOfCross hdisj ab) ∧
      Incident ab.2.val (edgeOfCross hdisj ab) := by
  unfold edgeOfCross
  split_ifs <;> simp [Incident]

theorem edgeOfCross_injective {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) : Function.Injective (edgeOfCross hdisj) := by
  intro ab cd heq
  by_cases hab : ab.1.val < ab.2.val
  · by_cases hcd : cd.1.val < cd.2.val
    · have hpair : (ab.1.val, ab.2.val) = (cd.1.val, cd.2.val) := by
        simpa [edgeOfCross, hab, hcd] using congrArg Subtype.val heq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst hpair)
      · exact Subtype.ext (congrArg Prod.snd hpair)
    · have hpair : (ab.1.val, ab.2.val) = (cd.2.val, cd.1.val) := by
        simpa [edgeOfCross, hab, hcd] using congrArg Subtype.val heq
      have hbad : ab.1.val = cd.2.val := congrArg Prod.fst hpair
      exact False.elim (Finset.disjoint_left.mp hdisj ab.1.property
        (hbad ▸ cd.2.property))
  · by_cases hcd : cd.1.val < cd.2.val
    · have hpair : (ab.2.val, ab.1.val) = (cd.1.val, cd.2.val) := by
        simpa [edgeOfCross, hab, hcd] using congrArg Subtype.val heq
      have hbad : cd.1.val = ab.2.val := (congrArg Prod.fst hpair).symm
      exact False.elim (Finset.disjoint_left.mp hdisj cd.1.property
        (hbad ▸ ab.2.property))
    · have hpair : (ab.2.val, ab.1.val) = (cd.2.val, cd.1.val) := by
        simpa [edgeOfCross, hab, hcd] using congrArg Subtype.val heq
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.snd hpair)
      · exact Subtype.ext (congrArg Prod.fst hpair)

/-- Edges between two disjoint vertex sets form an injective family inside
the complete graph, so their energy is bounded by the total energy. -/
theorem crossEnergy_le_complete {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) (p : ℝ) (z : Fin v → ℝ) :
    (∑ ab : CrossPair W O, EdgePower p z (edgeOfCross hdisj ab)) ≤
      CompleteEnergy p z := by
  classical
  let s : Finset (Edge v) :=
    Finset.univ.image (edgeOfCross hdisj : CrossPair W O → Edge v)
  have hsum :
      (∑ ab : CrossPair W O, EdgePower p z (edgeOfCross hdisj ab)) =
        ∑ e ∈ s, EdgePower p z e := by
    dsimp [s]
    exact (Finset.sum_image (s := (Finset.univ : Finset (CrossPair W O)))
      (g := edgeOfCross hdisj) (f := EdgePower p z)
      (fun _ _ _ _ h => edgeOfCross_injective hdisj h)).symm
  rw [hsum]
  unfold CompleteEnergy
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    exact Finset.mem_univ e
  · intro e _ _
    exact Real.rpow_nonneg (abs_nonneg _) _

/-- If a potential is constant on each side of a cut, the energy of that cut
is its edge count times the common edge power. -/
theorem crossEnergy_constant {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) (p a b : ℝ) (z : Fin v → ℝ)
    (hW : ∀ j ∈ W, z j = a) (hO : ∀ j ∈ O, z j = b) :
    (∑ ab : CrossPair W O, EdgePower p z (edgeOfCross hdisj ab)) =
      ((W.card * O.card : ℕ) : ℝ) * Real.rpow |a - b| p := by
  have hterm (ab : CrossPair W O) :
      EdgePower p z (edgeOfCross hdisj ab) = Real.rpow |a - b| p := by
    have ha := hW ab.1.val ab.1.property
    have hb := hO ab.2.val ab.2.property
    by_cases h : ab.1.val < ab.2.val
    · simp [edgeOfCross, h, EdgePower, ha, hb]
    · simp [edgeOfCross, h, EdgePower, ha, hb, abs_sub_comm]
  simp_rw [hterm]
  simp [CrossPair, Fintype.card_prod, mul_comm]

theorem edgePower_edgeOfCross {v : ℕ} {W O : Finset (Fin v)}
    (hdisj : Disjoint W O) (p : ℝ) (z : Fin v → ℝ)
    (ab : CrossPair W O) :
    EdgePower p z (edgeOfCross hdisj ab) =
      Real.rpow |z ab.1.val - z ab.2.val| p := by
  by_cases h : ab.1.val < ab.2.val
  · simp [edgeOfCross, h, EdgePower]
  · simp [edgeOfCross, h, EdgePower, abs_sub_comm]

/-- The support witness's selected cut has one center-outside edge and one
neighbor-outside edge per outside vertex. -/
theorem twoLevelCrossEnergy {v : ℕ} {W O : Finset (Fin v)}
    (u : Fin v) (huW : u ∉ W)
    (hdisj : Disjoint (insert u W) O)
    (p t : ℝ) (ht : 0 ≤ t)
    (z : Fin v → ℝ)
    (hu : z u = 1) (hW : ∀ j ∈ W, z j = t)
    (hO : ∀ j ∈ O, z j = 0) :
    (∑ ab : CrossPair (insert u W) O,
        EdgePower p z (edgeOfCross hdisj ab)) =
      (O.card : ℝ) * (1 + (W.card : ℝ) * Real.rpow t p) := by
  classical
  let T : ℝ := Real.rpow t p
  have hterm (ab : CrossPair (insert u W) O) :
      EdgePower p z (edgeOfCross hdisj ab) =
        if ab.1.val = u then 1 else T := by
    rw [edgePower_edgeOfCross]
    have hb := hO ab.2.val ab.2.property
    by_cases ha : ab.1.val = u
    · simp [ha, hu, hb, T, Real.rpow_eq_pow]
    · have haw : ab.1.val ∈ W :=
        (Finset.mem_insert.mp ab.1.property).resolve_left ha
      simp [ha, hW ab.1.val haw, hb, T, abs_of_nonneg ht]
  simp_rw [hterm]
  calc
    (∑ ab : CrossPair (insert u W) O,
        if ab.1.val = u then (1 : ℝ) else T) =
        ∑ a : {j : Fin v // j ∈ insert u W},
          (O.card : ℝ) * (if a.val = u then 1 else T) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a.val = u <;> simp [ha]
    _ = ∑ j ∈ insert u W,
          (O.card : ℝ) * (if j = u then 1 else T) := by
      exact (Finset.sum_subtype (insert u W) (by simp)
        (fun j => (O.card : ℝ) * (if j = u then 1 else T))).symm
    _ = (O.card : ℝ) * (1 + (W.card : ℝ) * T) := by
      rw [Finset.sum_insert huW]
      have hWsum :
          (∑ j ∈ W, (O.card : ℝ) * (if j = u then 1 else T)) =
            (W.card : ℝ) * ((O.card : ℝ) * T) := by
        calc
          (∑ j ∈ W, (O.card : ℝ) * (if j = u then 1 else T)) =
              ∑ _j ∈ W, (O.card : ℝ) * T := by
            apply Finset.sum_congr rfl
            intro j hj
            have hju : j ≠ u := by
              intro h
              exact huW (h ▸ hj)
            simp [hju]
          _ = (W.card : ℝ) * ((O.card : ℝ) * T) := by simp
      rw [hWsum]
      simp [T]
      ring

/-- The center and its supported neighbors contribute all selected
center-to-outside and neighbor-to-outside edges of the witness cut. -/
theorem witness_completeEnergy_lower_raw {v : ℕ}
    (p t : ℝ) (ht : 0 ≤ t) (w : Edge v → ℝ) (u : Fin v) :
    ((OutsideNeighbors w u).card : ℝ) *
        (1 + ((SupportNeighbors w u).card : ℝ) * Real.rpow t p) ≤
      CompleteEnergy p (WitnessPotential w u t) := by
  classical
  let W := SupportNeighbors w u
  let O := OutsideNeighbors w u
  have huW : u ∉ W := by
    intro hu
    have h := (Finset.mem_filter.mp hu).2.1
    exact h rfl
  have hdisj : Disjoint (insert u W) O := by
    apply Finset.disjoint_left.mpr
    intro j hj hjo
    have hju : j ≠ u := (Finset.mem_sdiff.mp hjo).1 |> Finset.mem_erase.mp |>.1
    have hjnot : j ∉ W := (Finset.mem_sdiff.mp hjo).2
    rcases Finset.mem_insert.mp hj with h | h
    · exact hju h
    · exact hjnot h
  have hW : ∀ j ∈ W, WitnessPotential w u t j = t := by
    intro j hj
    exact witness_at_neighbor w u j t hj
  have hO : ∀ j ∈ O, WitnessPotential w u t j = 0 := by
    intro j hj
    have hju : j ≠ u := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hj).1).1
    have hjnot : j ∉ W := (Finset.mem_sdiff.mp hj).2
    exact witness_at_outside w u j t hju hjnot
  have hcut := twoLevelCrossEnergy u huW hdisj p t ht
    (WitnessPotential w u t) (witness_at_center w u t) hW hO
  have hle := crossEnergy_le_complete hdisj p (WitnessPotential w u t)
  exact hcut ▸ hle

theorem inversePower_balance (p k : ℝ) (hp : 0 < p) (hk : 0 < k) :
    k * Real.rpow (Real.rpow k (-p⁻¹)) p = 1 := by
  have hexp : (-p⁻¹) * p = (-1 : ℝ) := by
    field_simp [ne_of_gt hp]
  calc
    k * Real.rpow (Real.rpow k (-p⁻¹)) p =
        k * Real.rpow k ((-p⁻¹) * p) := by
      congr 1
      simpa only [Real.rpow_eq_pow] using
        (Real.rpow_mul hk.le (-p⁻¹) p).symm
    _ = k * Real.rpow k (-1) := by rw [hexp]
    _ = 1 := by rw [Real.rpow_eq_pow, Real.rpow_neg_one];
                exact mul_inv_cancel₀ (ne_of_gt hk)

/-- The complete graph's support-dependent witness energy is at least twice
the number of missing edges at the chosen center. -/
theorem witness_completeEnergy_lower {v : ℕ}
    (p : ℝ) (hp : 0 < p) (w : Edge v → ℝ) (u : Fin v)
    (hk : 0 < SupportDegree w u) :
    2 * (((v - 1 : ℕ) : ℝ) - (SupportDegree w u : ℝ)) ≤
      CompleteEnergy p
        (WitnessPotential w u (Real.rpow (SupportDegree w u : ℝ) (-p⁻¹))) := by
  let k : ℝ := (SupportDegree w u : ℝ)
  let t : ℝ := Real.rpow k (-p⁻¹)
  have hkR : 0 < k := Nat.cast_pos.mpr hk
  have ht : 0 ≤ t := (Real.rpow_pos_of_pos hkR _).le
  have hbal : k * Real.rpow t p = 1 := inversePower_balance p k hp hkR
  have hraw := witness_completeEnergy_lower_raw p t ht w u
  have hcard : ((OutsideNeighbors w u).card : ℝ) =
      ((v - 1 : ℕ) : ℝ) - k := by
    rw [outside_card]
    exact Nat.cast_sub (supportDegree_le w u)
  calc
    2 * (((v - 1 : ℕ) : ℝ) - (SupportDegree w u : ℝ)) =
        ((OutsideNeighbors w u).card : ℝ) *
          (1 + ((SupportNeighbors w u).card : ℝ) * Real.rpow t p) := by
      rw [hcard]
      change 2 * (((v - 1 : ℕ) : ℝ) - k) =
        (((v - 1 : ℕ) : ℝ) - k) * (1 + k * Real.rpow t p)
      rw [hbal]
      ring
    _ ≤ CompleteEnergy p (WitnessPotential w u t) := hraw

noncomputable def NeighborIncidenceWeight {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) (e : Edge v) : ℝ :=
  ∑ j ∈ SupportNeighbors w u,
    if Incident j e then w e else 0

theorem neighborIncidenceWeight_nonneg {v : ℕ}
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (u : Fin v) (e : Edge v) :
    0 ≤ NeighborIncidenceWeight w u e := by
  unfold NeighborIncidenceWeight
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hw e
  · exact le_refl _

theorem edgeWeight_le_neighborIncidence_of_mem {v : ℕ}
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (u j : Fin v) (e : Edge v)
    (hj : j ∈ SupportNeighbors w u) (hje : Incident j e) :
    w e ≤ NeighborIncidenceWeight w u e := by
  unfold NeighborIncidenceWeight
  have hsingle := Finset.single_le_sum
    (s := SupportNeighbors w u)
    (f := fun j => if Incident j e then w e else 0)
    (fun j _ => by split_ifs; exact hw e; exact le_refl _) hj
  simpa [hje] using hsingle

private theorem witness_edgePower_noncenter {v : ℕ}
    (p t : ℝ) (hp : 0 < p) (ht : 0 ≤ t)
    (w : Edge v → ℝ) (u : Fin v) (e : Edge v)
    (ha : e.val.1 ≠ u) (hb : e.val.2 ≠ u) :
    EdgePower p (WitnessPotential w u t) e =
      if (e.val.1 ∈ SupportNeighbors w u) =
          (e.val.2 ∈ SupportNeighbors w u) then 0
      else Real.rpow t p := by
  classical
  by_cases hWa : e.val.1 ∈ SupportNeighbors w u
  · by_cases hWb : e.val.2 ∈ SupportNeighbors w u
    · simp [EdgePower, WitnessPotential, ha, hb, hWa, hWb,
        Real.rpow_eq_pow, hp.ne']
    · simp [EdgePower, WitnessPotential, ha, hb, hWa, hWb,
        abs_of_nonneg ht]
  · by_cases hWb : e.val.2 ∈ SupportNeighbors w u
    · simp [EdgePower, WitnessPotential, ha, hb, hWa, hWb,
        abs_of_nonneg ht]
    · simp [EdgePower, WitnessPotential, ha, hb, hWa, hWb,
        Real.rpow_eq_pow, hp.ne']

private theorem positive_edge_center_neighbor {v : ℕ}
    (w : Edge v → ℝ) (u : Fin v) (e : Edge v)
    (hwe : 0 < w e) :
    (e.val.1 = u → e.val.2 ∈ SupportNeighbors w u) ∧
      (e.val.2 = u → e.val.1 ∈ SupportNeighbors w u) := by
  classical
  constructor
  · intro ha
    have hne : e.val.2 ≠ u := by
      intro hb
      exact (ne_of_lt e.property) (ha.trans hb.symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨hne, e, Or.inl ha, Or.inr rfl, hwe⟩⟩
  · intro hb
    have hne : e.val.1 ≠ u := by
      intro ha
      exact (ne_of_lt e.property) (ha.trans hb.symm)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ⟨hne, e, Or.inr hb, Or.inl rfl, hwe⟩⟩

private theorem witness_edgePower_center {v : ℕ}
    (p t : ℝ) (ht1 : t ≤ 1)
    (w : Edge v → ℝ) (u : Fin v) (e : Edge v)
    (hwe : 0 < w e) (hinc : Incident u e) :
    EdgePower p (WitnessPotential w u t) e =
      Real.rpow (1 - t) p := by
  classical
  have hneighbor := positive_edge_center_neighbor w u e hwe
  rcases hinc with ha | hb
  · have hWb := hneighbor.1 ha
    have hne : e.val.2 ≠ u := by
      intro h
      exact (ne_of_lt e.property) (ha.trans h.symm)
    simp [EdgePower, WitnessPotential, ha, hne, hWb,
      abs_of_nonneg (by linarith : 0 ≤ 1 - t)]
  · have hWa := hneighbor.2 hb
    have hne : e.val.1 ≠ u := by
      intro h
      exact (ne_of_lt e.property) (h.trans hb.symm)
    simp [EdgePower, WitnessPotential, hb, hne, hWa]
    rw [abs_sub_comm t 1, abs_of_nonneg (by linarith : 0 ≤ 1 - t)]

/-- Each weighted witness edge is charged either to the center's weighted
degree or to a supported neighbor's weighted degree. -/
theorem witness_edge_upper {v : ℕ}
    (p t : ℝ) (hp : 0 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (u : Fin v) (e : Edge v) :
    w e * EdgePower p (WitnessPotential w u t) e ≤
      (if Incident u e then w e * Real.rpow (1 - t) p else 0) +
        Real.rpow t p * NeighborIncidenceWeight w u e := by
  classical
  have htpow : 0 ≤ Real.rpow t p := Real.rpow_nonneg ht0 p
  have hsum : 0 ≤ NeighborIncidenceWeight w u e :=
    neighborIncidenceWeight_nonneg w hw u e
  by_cases hzero : w e = 0
  · simp [hzero, NeighborIncidenceWeight]
  have hwe : 0 < w e := lt_of_le_of_ne (hw e) (Ne.symm hzero)
  by_cases hinc : Incident u e
  · rw [witness_edgePower_center p t ht1 w u e hwe hinc]
    simp only [if_pos hinc]
    exact le_add_of_nonneg_right (mul_nonneg htpow hsum)
  · have ha : e.val.1 ≠ u := by
      intro h
      exact hinc (Or.inl h)
    have hb : e.val.2 ≠ u := by
      intro h
      exact hinc (Or.inr h)
    rw [witness_edgePower_noncenter p t hp ht0 w u e ha hb]
    simp only [if_neg hinc, zero_add]
    by_cases hsame :
        (e.val.1 ∈ SupportNeighbors w u) =
          (e.val.2 ∈ SupportNeighbors w u)
    · rw [if_pos hsame, mul_zero]
      exact mul_nonneg htpow hsum
    · rw [if_neg hsame]
      have hW : e.val.1 ∈ SupportNeighbors w u ∨
          e.val.2 ∈ SupportNeighbors w u := by
        by_cases hWa : e.val.1 ∈ SupportNeighbors w u
        · exact Or.inl hWa
        · right
          by_contra hWb
          exact hsame (propext ⟨(fun h => False.elim (hWa h)),
            (fun h => False.elim (hWb h))⟩)
      have hweight : w e ≤ NeighborIncidenceWeight w u e := by
        rcases hW with hWa | hWb
        · exact edgeWeight_le_neighborIncidence_of_mem w hw u e.val.1 e hWa
            (Or.inl rfl)
        · exact edgeWeight_le_neighborIncidence_of_mem w hw u e.val.2 e hWb
            (Or.inr rfl)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hweight htpow

/-- Summing the edgewise charge bounds the witness energy by weighted
degrees at the center and its supported neighbors. -/
theorem witness_weightedEnergy_upper_degrees {v : ℕ}
    (p t : ℝ) (hp : 0 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e) (u : Fin v) :
    WeightedEnergy p w (WitnessPotential w u t) ≤
      Real.rpow (1 - t) p *
        (∑ e ∈ Finset.univ.filter (Incident u), w e) +
      Real.rpow t p *
        (∑ j ∈ SupportNeighbors w u,
          ∑ e ∈ Finset.univ.filter (Incident j), w e) := by
  classical
  unfold WeightedEnergy
  have hcenter :
      (∑ e : Edge v, if Incident u e then w e * Real.rpow (1 - t) p else 0) =
        Real.rpow (1 - t) p *
          (∑ e ∈ Finset.univ.filter (Incident u), w e) := by
    simp [Finset.sum_ite, Finset.mul_sum, mul_comm]
  have hneighbor :
      (∑ e : Edge v, NeighborIncidenceWeight w u e) =
        ∑ j ∈ SupportNeighbors w u,
          ∑ e ∈ Finset.univ.filter (Incident j), w e := by
    calc
      (∑ e : Edge v, NeighborIncidenceWeight w u e) =
          ∑ e : Edge v, ∑ j ∈ SupportNeighbors w u,
            if Incident j e then w e else 0 := rfl
      _ = ∑ j ∈ SupportNeighbors w u, ∑ e : Edge v,
            if Incident j e then w e else 0 := Finset.sum_comm
      _ = ∑ j ∈ SupportNeighbors w u,
            ∑ e ∈ Finset.univ.filter (Incident j), w e := by
        simp [Finset.sum_ite]
  calc
    (∑ e : Edge v, w e * EdgePower p (WitnessPotential w u t) e) ≤
        ∑ e : Edge v,
          ((if Incident u e then w e * Real.rpow (1 - t) p else 0) +
            Real.rpow t p * NeighborIncidenceWeight w u e) := by
      apply Finset.sum_le_sum
      intro e _
      exact witness_edge_upper p t hp ht0 ht1 w hw u e
    _ = Real.rpow (1 - t) p *
          (∑ e ∈ Finset.univ.filter (Incident u), w e) +
        Real.rpow t p *
          (∑ j ∈ SupportNeighbors w u,
            ∑ e ∈ Finset.univ.filter (Incident j), w e) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcenter, hneighbor]

/-- Singleton tests control every degree in the edgewise witness bound. -/
theorem witness_weightedEnergy_upper_raw {v : ℕ}
    (p ε t : ℝ) (hp : 0 < p) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    WeightedEnergy p w (WitnessPotential w u t) ≤
      (1 + ε) * ((v - 1 : ℕ) : ℝ) *
        (Real.rpow (1 - t) p +
          (SupportDegree w u : ℝ) * Real.rpow t p) := by
  let R : ℝ := ((v - 1 : ℕ) : ℝ)
  let k : ℝ := (SupportDegree w u : ℝ)
  let zpow : ℝ := Real.rpow (1 - t) p
  let tpow : ℝ := Real.rpow t p
  have hzpow : 0 ≤ zpow := Real.rpow_nonneg (by linarith : 0 ≤ 1 - t) p
  have htpow : 0 ≤ tpow := Real.rpow_nonneg ht0 p
  have hcenter := (weightedDegree_bounds_exact p ε hp w happrox u).2
  have hneighbors :
      (∑ j ∈ SupportNeighbors w u,
          ∑ e ∈ Finset.univ.filter (Incident j), w e) ≤
        k * ((1 + ε) * R) := by
    calc
      (∑ j ∈ SupportNeighbors w u,
          ∑ e ∈ Finset.univ.filter (Incident j), w e) ≤
          ∑ _j ∈ SupportNeighbors w u, (1 + ε) * R := by
        apply Finset.sum_le_sum
        intro j _
        exact (weightedDegree_bounds_exact p ε hp w happrox j).2
      _ = k * ((1 + ε) * R) := by simp [k, SupportDegree]
  have hupper := witness_weightedEnergy_upper_degrees p t hp ht0 ht1 w hw u
  calc
    WeightedEnergy p w (WitnessPotential w u t) ≤
        zpow * (∑ e ∈ Finset.univ.filter (Incident u), w e) +
          tpow * (∑ j ∈ SupportNeighbors w u,
            ∑ e ∈ Finset.univ.filter (Incident j), w e) := hupper
    _ ≤ zpow * ((1 + ε) * R) + tpow * (k * ((1 + ε) * R)) :=
      add_le_add (mul_le_mul_of_nonneg_left hcenter hzpow)
        (mul_le_mul_of_nonneg_left hneighbors htpow)
    _ = (1 + ε) * R * (zpow + k * tpow) := by ring

/-- The balanced support witness has the source's weighted-energy upper
bound, valid for arbitrary nonnegative edge weights. -/
theorem witness_weightedEnergy_upper {v : ℕ}
    (p ε : ℝ) (hp : 0 < p)
    (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) (hk : 0 < SupportDegree w u) :
    WeightedEnergy p w
        (WitnessPotential w u (Real.rpow (SupportDegree w u : ℝ) (-p⁻¹))) ≤
      (1 + ε) * ((v - 1 : ℕ) : ℝ) *
        (1 + Real.rpow
          (1 - Real.rpow (SupportDegree w u : ℝ) (-p⁻¹)) p) := by
  let k : ℝ := (SupportDegree w u : ℝ)
  let t : ℝ := Real.rpow k (-p⁻¹)
  have hkR : 0 < k := Nat.cast_pos.mpr hk
  have hk1 : 1 ≤ k := by
    have hkNat : 1 ≤ SupportDegree w u := hk
    change (1 : ℝ) ≤ (SupportDegree w u : ℝ)
    exact_mod_cast hkNat
  have ht0 : 0 ≤ t := (Real.rpow_pos_of_pos hkR _).le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    simpa only [Real.rpow_eq_pow] using
      Real.rpow_le_one_of_one_le_of_nonpos hk1
        (neg_nonpos.mpr (inv_pos.mpr hp).le)
  have hraw := witness_weightedEnergy_upper_raw p ε t hp ht0 ht1 w hw happrox u
  have hbal : k * Real.rpow t p = 1 := inversePower_balance p k hp hkR
  calc
    WeightedEnergy p w (WitnessPotential w u t) ≤
        (1 + ε) * ((v - 1 : ℕ) : ℝ) *
          (Real.rpow (1 - t) p + k * Real.rpow t p) := hraw
    _ = (1 + ε) * ((v - 1 : ℕ) : ℝ) *
          (1 + Real.rpow (1 - t) p) := by rw [hbal]; ring

/-- Every successful nonnegative weighted complete graph has the source's
support-degree obstruction at each vertex. -/
theorem supportDegree_lower_of_approx {v : ℕ}
    (p ε : ℝ) (hp : 1 < p) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hv : 1 < v) (w : Edge v → ℝ) (hw : ∀ e, 0 ≤ w e)
    (happrox : ∀ z : Fin v → ℝ,
      (1 - ε) * CompleteEnergy p z ≤ WeightedEnergy p w z ∧
      WeightedEnergy p w z ≤ (1 + ε) * CompleteEnergy p z)
    (u : Fin v) :
    ((v - 1 : ℕ) : ℝ) * ε ≤ (SupportDegree w u : ℝ) ∨
      Real.rpow (6 * ε) (-p) ≤ (SupportDegree w u : ℝ) := by
  have hp0 : 0 < p := by linarith
  have hk := supportDegree_pos p ε hp0 (by linarith) hv w hw happrox u
  have hk1 : 1 ≤ (SupportDegree w u : ℝ) := by
    have hNat : 1 ≤ SupportDegree w u := hk
    exact_mod_cast hNat
  have hR : 0 < ((v - 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.sub_pos_of_lt hv)
  let t : ℝ := Real.rpow (SupportDegree w u : ℝ) (-p⁻¹)
  let z := WitnessPotential w u t
  have hF := witness_completeEnergy_lower p hp0 w u hk
  have hU := witness_weightedEnergy_upper p ε hp0 w hw happrox u hk
  have happroxLower := (happrox z).1
  have hcompare :
      (1 - ε) *
        (2 * (((v - 1 : ℕ) : ℝ) - (SupportDegree w u : ℝ))) ≤
      (1 + ε) * ((v - 1 : ℕ) : ℝ) *
        (1 + Real.rpow
          (1 - Real.rpow (SupportDegree w u : ℝ) (-p⁻¹)) p) := by
    calc
      (1 - ε) * (2 * (((v - 1 : ℕ) : ℝ) - (SupportDegree w u : ℝ))) ≤
          (1 - ε) * CompleteEnergy p z :=
        mul_le_mul_of_nonneg_left hF (by linarith)
      _ ≤ WeightedEnergy p w z := happroxLower
      _ ≤ (1 + ε) * ((v - 1 : ℕ) : ℝ) *
          (1 + Real.rpow
            (1 - Real.rpow (SupportDegree w u : ℝ) (-p⁻¹)) p) := hU
  exact weakWitnessComparison_forces_support_bound p ε
    ((v - 1 : ℕ) : ℝ) (SupportDegree w u : ℝ)
    hp hε hR hk1 hcompare

#print axioms edgeOfCross_injective
#print axioms crossEnergy_le_complete
#print axioms crossEnergy_constant
#print axioms twoLevelCrossEnergy
#print axioms witness_completeEnergy_lower_raw
#print axioms inversePower_balance
#print axioms witness_completeEnergy_lower
#print axioms edgeWeight_le_neighborIncidence_of_mem
#print axioms witness_edge_upper
#print axioms witness_weightedEnergy_upper_degrees
#print axioms witness_weightedEnergy_upper_raw
#print axioms witness_weightedEnergy_upper
#print axioms supportDegree_lower_of_approx

end NLA.Proofs.RA06
