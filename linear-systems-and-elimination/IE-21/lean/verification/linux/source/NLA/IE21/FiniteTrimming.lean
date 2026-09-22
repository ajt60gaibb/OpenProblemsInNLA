import NLA.IE21.MatrixSemantics

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal Topology
namespace NLA.IE21

theorem finiteTrim_minimum {m : ℕ} (k : ℕ) (hk : k ≤ m) (y : Fin m → ℝ) :
    (∃ S : Finset (Fin m), S.card = k ∧ finiteTrim k y = ∑ i ∈ S, y i) ∧
    (∀ S : Finset (Fin m), S.card = k → finiteTrim k y ≤ ∑ i ∈ S, y i) := by
  classical
  let Z : Set ℝ := {z | ∃ S : Finset (Fin m), S.card = k ∧ z = ∑ i ∈ S, y i}
  have hf : Z.Finite := (Set.finite_range (fun S : Finset (Fin m) => ∑ i ∈ S, y i)).subset
    (by rintro z ⟨S, hS, rfl⟩; exact ⟨S, rfl⟩)
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (n := k) (by simpa using hk)
  have hne : Z.Nonempty := ⟨_, S, hS, rfl⟩
  have hmem := hne.csInf_mem hf
  obtain ⟨T, hT, heq⟩ := hmem
  refine ⟨⟨T, hT, heq⟩, ?_⟩
  intro U hU
  exact csInf_le hf.bddBelow ⟨U, hU, rfl⟩

theorem trimDual_eq_div {m : ℕ} (k : ℕ) (y : Fin m → ℝ) (t : ℝ) :
    trimDual k y t = ((k : ℝ) * t - ∑ i, max (t - y i) 0) / m := by
  unfold trimDual
  ring

theorem trimDual_le_selection {m : ℕ} (_hm : 1 ≤ m) (k : ℕ)
    (y : Fin m → ℝ) (S : Finset (Fin m)) (hS : S.card = k) (t : ℝ) :
    trimDual k y t ≤ (∑ i ∈ S, y i) / m := by
  classical
  have hsum₁ : (∑ i ∈ S, (t - y i)) ≤ ∑ i ∈ S, max (t - y i) 0 :=
    Finset.sum_le_sum fun i hi => le_max_left _ _
  have hsum₂ : (∑ i ∈ S, max (t - y i) 0) ≤ ∑ i, max (t - y i) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => le_max_right _ _)
  have hsum : (∑ i ∈ S, (t - y i)) = (k : ℝ) * t - ∑ i ∈ S, y i := by
    simp [Finset.sum_sub_distrib, hS]
  rw [trimDual_eq_div]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg m)
  linarith

theorem minimizing_selection_order {m : ℕ} (k : ℕ) (y : Fin m → ℝ)
    (S : Finset (Fin m)) (hS : S.card = k)
    (hmin : ∀ T : Finset (Fin m), T.card = k → (∑ i ∈ S, y i) ≤ ∑ i ∈ T, y i)
    (i j : Fin m) (hi : i ∈ S) (hj : j ∉ S) : y i ≤ y j := by
  classical
  have hj' : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hp : 0 < S.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hcard : (insert j (S.erase i)).card = k := by
    rw [Finset.card_insert_of_notMem hj', Finset.card_erase_of_mem hi]
    omega
  have h := hmin (insert j (S.erase i)) hcard
  rw [Finset.sum_insert hj'] at h
  have he := Finset.sum_erase_add S y hi
  linarith

theorem finite_trimming_semantics {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) :
    (∃ S : Finset (Fin m), S.card = k ∧ finiteTrim k y = ∑ i ∈ S, y i) ∧
    (∀ S : Finset (Fin m), S.card = k → finiteTrim k y ≤ ∑ i ∈ S, y i) ∧
    (∃ t : ℝ, 0 ≤ t ∧ finiteTrim k y / m = trimDual k y t ∧
      ∀ u : ℝ, 0 ≤ u → trimDual k y u ≤ trimDual k y t) := by
  classical
  obtain ⟨⟨S, hS, hval⟩, hmin⟩ := finiteTrim_minimum k hk y
  refine ⟨⟨S, hS, hval⟩, hmin, ?_⟩
  have horder : ∀ i ∈ S, ∀ j ∉ S, y i ≤ y j := by
    intro i hi j hj
    apply minimizing_selection_order k y S hS _ i j hi hj
    intro T hT
    simpa [← hval] using hmin T hT
  obtain ⟨t, ht, hin, hout⟩ : ∃ t : ℝ, 0 ≤ t ∧
      (∀ i ∈ S, y i ≤ t) ∧ (∀ j ∉ S, t ≤ y j) := by
    rcases S.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, le_rfl, by simp, fun j _ => hy j⟩
    · refine ⟨S.sup' hne y, ?_, ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact (hy i).trans (Finset.le_sup' y hi)
      · intro i hi
        exact Finset.le_sup' y hi
      · intro j hj
        obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hne y
        rw [heq]
        exact horder i hi j hj
  have hsum : (∑ i, max (t - y i) 0) = (k : ℝ) * t - ∑ i ∈ S, y i := by
    calc
      (∑ i, max (t - y i) 0) = ∑ i ∈ S, max (t - y i) 0 := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        exact max_eq_right (sub_nonpos.mpr (hout i hi))
      _ = ∑ i ∈ S, (t - y i) :=
        Finset.sum_congr rfl fun i hi => max_eq_left (sub_nonneg.mpr (hin i hi))
      _ = _ := by simp [Finset.sum_sub_distrib, hS]
  have heq : finiteTrim k y / m = trimDual k y t := by
    rw [trimDual_eq_div, hsum, hval]
    ring
  refine ⟨t, ht, heq, ?_⟩
  intro u _
  rw [← heq, hval]
  exact trimDual_le_selection hm k y S hS u

theorem directional_minimum {m n : ℕ} (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (A : Mat m n) (_hm : 1 ≤ m) (hn : 1 ≤ n) :
    (∃ x : Space n, ‖x‖ = 1 ∧ directionalTrim θ A x = normalizedDeletion θ A) ∧
      (∀ x : Space n, ‖x‖ = 1 → normalizedDeletion θ A ≤ directionalTrim θ A x) := by
  have hc : 0 ≤ (n : ℝ) / m := div_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)
  obtain ⟨h0, ⟨S, x, hS, hx, hval⟩, hmin⟩ := deletion_minimum θ hθ A hn
  have hlower : ∀ y : Space n, ‖y‖ = 1 →
      deletionSingular θ A ^ 2 ≤
        finiteTrim (retainedRows θ m) (fun i => (matrixMap A y i) ^ 2) := by
    intro y hy
    obtain ⟨⟨T, hT, hTy⟩, _⟩ := finiteTrim_minimum (retainedRows θ m)
      (retainedRows_le θ hθ m) (fun i => (matrixMap A y i) ^ 2)
    rw [hTy, ← retainedNorm_sq]
    exact pow_le_pow_left₀ h0 (hmin T y hT hy) 2
  refine ⟨⟨x, hx, ?_⟩, ?_⟩
  · have hupper := (finiteTrim_minimum (retainedRows θ m) (retainedRows_le θ hθ m)
      (fun i => (matrixMap A x i) ^ 2)).2 S hS
    rw [← retainedNorm_sq, ← hval] at hupper
    have heq := le_antisymm hupper (hlower x hx)
    simp only [directionalTrim, normalizedDeletion, heq]
  · intro y hy
    exact mul_le_mul_of_nonneg_left (hlower y hy) hc

local instance (m : ℕ) : TopologicalSpace (Finset (Fin m)) := ⊥
local instance (m : ℕ) : DiscreteTopology (Finset (Fin m)) := ⟨rfl⟩

theorem continuous_finiteTrim (m k : ℕ) : Continuous (finiteTrim (m := m) k) := by
  classical
  have heq : finiteTrim (m := m) k = fun y =>
      sInf ((fun S : Finset (Fin m) => ∑ i ∈ S, y i) '' {S | S.card = k}) := by
    funext y
    unfold finiteTrim
    congr 1
    ext z
    constructor
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, hS, rfl⟩
    · rintro ⟨S, hS, rfl⟩
      exact ⟨S, hS, rfl⟩
  rw [heq]
  apply (Set.toFinite {S : Finset (Fin m) | S.card = k}).isCompact.continuous_sInf
  apply continuous_prod_of_discrete_right.mpr
  intro S
  change Continuous (fun y : Fin m → ℝ => ∑ i ∈ S, y i)
  fun_prop

theorem continuous_directionalTrim {m n : ℕ} (θ : ℝ) (x : Space n) :
    Continuous (fun A : Mat m n => directionalTrim θ A x) := by
  have hc : Continuous (fun A : Mat m n => fun i => (matrixMap A x i) ^ 2) := by
    simp only [matrixMap_apply]
    fun_prop
  exact continuous_const.mul ((continuous_finiteTrim m (retainedRows θ m)).comp hc)

theorem continuous_covarianceError (m n : ℕ) :
    Continuous (covarianceError (m := m) (n := n)) := by
  have hc := continuous_matrixMap m n
  have ha : Continuous (fun A : Mat m n => (matrixMap A).adjoint) :=
    ContinuousLinearMap.adjoint.continuous.comp hc
  have hc' : Continuous (fun A : Mat m n => (matrixMap A).adjoint.comp (matrixMap A)) :=
    ha.clm_comp hc
  have hs : Continuous (fun A : Mat m n => ((n : ℝ) / m) •
      ((matrixMap A).adjoint.comp (matrixMap A))) := by
    convert (continuous_const (y := (n : ℝ) / m)).smul hc' using 1
    funext A
    rfl
  have hd := hs.sub (continuous_const (y := ContinuousLinearMap.id ℝ (Space n)))
  convert hd.norm using 1
  funext A
  rfl

theorem statistics_measurable (m n : ℕ) (θ : ℝ) (_hθ : 0 < θ ∧ θ < 1)
    (_hn : 1 ≤ n) :
    Measurable (deletionSingular (m := m) (n := n) θ) ∧
    Measurable (operatorNorm (m := m) (n := n)) ∧
    Measurable (deletionRatio (m := m) (n := n) θ) ∧
    ∀ t ε δ, MeasurableSet (GoodEvent θ m n t ε δ) := by
  have hd := (continuous_deletionSingular m n θ).measurable
  have ho : Measurable (operatorNorm (m := m) (n := n)) :=
    (continuous_matrixMap m n).norm.measurable
  refine ⟨hd, ho, (hd.pow_const 2).div (ho.pow_const 2), ?_⟩
  intro t ε δ
  apply IsClosed.measurableSet
  have heq : GoodEvent θ m n t ε δ =
      {A : Mat m n | covarianceError A ≤ t} ∩
        ⋂ x : Space n, ⋂ (_hx : ‖x‖ = 1),
          {A : Mat m n | |directionalTrim θ A x - gaussianTrim θ| ≤
            trimmingError θ m t ε δ + Real.sqrt (2 / (n : ℝ))} := by
    ext A
    simp [GoodEvent]
  rw [heq]
  refine (isClosed_le (continuous_covarianceError m n) continuous_const).inter ?_
  apply isClosed_iInter
  intro x
  apply isClosed_iInter
  intro _
  exact isClosed_le ((continuous_directionalTrim θ x).sub continuous_const).abs continuous_const

end NLA.IE21
