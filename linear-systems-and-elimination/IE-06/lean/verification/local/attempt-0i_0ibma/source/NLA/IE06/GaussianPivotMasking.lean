import NLA.IE06.GaussianPivotConditioning

/-! A measurable outside-row pivot candidate by literal zero masking.
Preimplementation contract: reviews/gaussian-pivot-masking-contract.md. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Set
namespace NLA.IE06.GaussianPivotMasking
open GaussianPivotConditioning

/-- Suppress rows according to their current original labels. -/
def maskLabels {n : ℕ} (S : Finset (Fin n)) (L : Fin n → Fin n) (A : Mat n) : Mat n :=
  fun i j => if L i ∈ S then 0 else A i j

/-- A fixed coordinate projection, independent of the suppressed input rows. -/
def zeroMasked {n : ℕ} (S : Finset (Fin n)) (A : Mat n) : Mat n := maskLabels S id A

theorem measurable_zeroMasked {n : ℕ} (S : Finset (Fin n)) : Measurable (zeroMasked S) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hi : i ∈ S
  · simpa only [zeroMasked, maskLabels, id_eq, hi, if_true] using
      (measurable_const : Measurable (fun _ : Mat n => (0 : ℝ)))
  · simpa only [zeroMasked, maskLabels, id_eq, hi, if_false] using measurable_matrix_entry i j

theorem zeroMasked_eq_of_outside_eq {n : ℕ} (S : Finset (Fin n)) (A B : Mat n)
    (h : ∀ i : Fin n, i ∉ S → ∀ j : Fin n, A i j = B i j) : zeroMasked S A = zeroMasked S B := by
  funext i j
  by_cases hi : i ∈ S
  · simp [zeroMasked, maskLabels, hi]
  · simp [zeroMasked, maskLabels, hi, h i hi j]

theorem maskLabels_schurStep {n : ℕ} (S : Finset (Fin n)) (L : Fin n → Fin n)
    (A : Mat n) (k p : Fin n) (hp : L p ∉ S) :
    schurStep (maskLabels S L A) k p =
      maskLabels S (L ∘ Equiv.swap k p) (schurStep A k p) := by
  funext i j
  by_cases hactive : k < i ∧ k < j
  · simp only [schurStep, hactive, rowSwap, maskLabels, Function.comp_apply,
      Equiv.swap_apply_left, hp, if_false]
    by_cases hi : L (Equiv.swap k p i) ∈ S <;> simp [hi]
  · simp only [schurStep, hactive, if_false, maskLabels]
    split_ifs <;> rfl

/-- Positive surviving maxima retain the exact frozen least-current-index tie
rule after other original rows have been replaced by zero. -/
theorem firstPivotIndex_maskLabels {n : ℕ} (S : Finset (Fin n)) (L : Fin n → Fin n)
    (A : Mat n) (k : Fin n) (hp : L (firstPivotIndex A k) ∉ S)
    (hnz : A (firstPivotIndex A k) k ≠ 0) :
    firstPivotIndex (maskLabels S L A) k = firstPivotIndex A k := by
  let p := firstPivotIndex A k
  have hs := firstPivotIndex_spec_proved A k
  change L p ∉ S at hp
  have hpk : maskLabels S L A p k = A p k := by simp only [maskLabels, hp, if_false]
  apply firstPivotIndex_eq_of_firstAvailable_proved
  refine ⟨⟨hs.1, ?_, ?_⟩, ?_⟩
  · rwa [hpk]
  · intro i hi
    rw [hpk]
    by_cases hS : L i ∈ S
    · simp only [maskLabels, hS, if_true, abs_zero]
      exact abs_nonneg _
    · simpa only [maskLabels, hS, if_false] using hs.2.1 i hi
  · intro i hi he
    rw [hpk] at he
    by_cases hS : L i ∈ S
    · simp only [maskLabels, hS, if_true, abs_zero] at he
      exact False.elim ((abs_pos.mpr hnz).ne he)
    · simp only [maskLabels, hS, if_false] at he
      exact hs.2.2 i hi he

/-- Exact masked state through a nonzero pivot prefix that avoids the removed
original rows. No assumption about the masked matrix's determinant is made. -/
theorem firstTrajectory_zeroMasked {n m : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) (A : Mat n)
    (havoid : ∀ j : Fin m, pivotOrder hm A j ∉ S)
    (hnz : ∀ j : Fin m,
      firstTrajectory A j.val (firstPath A (Fin.castLE hm j)) (Fin.castLE hm j) ≠ 0)
    (s : ℕ) (hs : s ≤ m) :
    firstTrajectory (zeroMasked S A) s =
      maskLabels S (rowLabels (firstPath A) s) (firstTrajectory A s) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hsm : s < m := by omega
      let j : Fin m := ⟨s,hsm⟩
      let k := Fin.castLE hm j
      have hsn : s < n := k.isLt
      have hprev := ih (by omega)
      have hp : rowLabels (firstPath A) s (firstPath A k) ∉ S := by
        simpa only [pivotOrder_stage hm A j] using havoid j
      have hchoice : firstPivotIndex (firstTrajectory (zeroMasked S A) s) k = firstPath A k := by
        rw [hprev]
        exact firstPivotIndex_maskLabels S _ _ k hp (hnz j)
      have hk : (⟨s,hsn⟩ : Fin n) = k := rfl
      rw [firstTrajectory, dif_pos hsn, hk, hchoice, hprev,
        maskLabels_schurStep S _ _ k (firstPath A k) hp]
      rw [firstTrajectory, dif_pos hsn]
      have hl : (fun i => rowLabels (firstPath A) s (Equiv.swap k (firstPath A k) i)) =
          rowLabels (firstPath A) (s+1) := by
        funext i
        exact (rowLabels_succ (firstPath A) k i).symm
      rw [show (rowLabels (firstPath A) s : Fin n → Fin n) ∘ Equiv.swap k (firstPath A k) =
        rowLabels (firstPath A) (s+1) from hl]
      rfl

theorem firstPath_zeroMasked_prefix {n m : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) (A : Mat n)
    (havoid : ∀ j : Fin m, pivotOrder hm A j ∉ S)
    (hnz : ∀ j : Fin m,
      firstTrajectory A j.val (firstPath A (Fin.castLE hm j)) (Fin.castLE hm j) ≠ 0)
    (j : Fin m) : firstPath (zeroMasked S A) (Fin.castLE hm j) = firstPath A (Fin.castLE hm j) := by
  change firstPivotIndex (firstTrajectory (zeroMasked S A) j.val) (Fin.castLE hm j) = _
  rw [firstTrajectory_zeroMasked hm S A havoid hnz j.val j.isLt.le]
  apply firstPivotIndex_maskLabels
  · change rowLabels (firstPath A) j.val (firstPath A (Fin.castLE hm j)) ∉ S
    simpa only [pivotOrder_stage hm A j] using havoid j
  · exact hnz j

theorem pivotOrder_zeroMasked {n m : ℕ} (hm : m ≤ n) (S : Finset (Fin n)) (A : Mat n)
    (havoid : ∀ j : Fin m, pivotOrder hm A j ∉ S)
    (hnz : ∀ j : Fin m,
      firstTrajectory A j.val (firstPath A (Fin.castLE hm j)) (Fin.castLE hm j) ≠ 0) :
    pivotOrder hm (zeroMasked S A) = pivotOrder hm A := by
  have hp : rowLabels (firstPath (zeroMasked S A)) m = rowLabels (firstPath A) m := by
    apply rowLabels_prefix_congr
    intro j hj
    exact firstPath_zeroMasked_prefix hm S A havoid hnz ⟨j.val,hj⟩
  apply DFunLike.ext
  intro j
  exact congrArg (fun L : Equiv.Perm (Fin n) => L (Fin.castLE hm j)) hp


abbrev OutsideRows {n : ℕ} (S : Finset (Fin n)) := {i : Fin n // i ∉ S}

theorem outsideRows_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (OutsideRows S) = n-S.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  exact Fintype.card_coe S

/-- A fixed outside-row injection, independent of every input matrix. -/
def fallbackOrder {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card) : Fin m ↪ OutsideRows S :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, outsideRows_card]
    exact hm))

/-- A total measurable candidate, always selecting distinct outside-S labels. -/
def candidateOrder {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card) (A : Mat n) :
    Fin m ↪ OutsideRows S :=
  if h : ∀ j : Fin m,
      pivotOrder (hm.trans (Nat.sub_le n S.card)) (zeroMasked S A) j ∉ S then
    { toFun := fun j => ⟨pivotOrder (hm.trans (Nat.sub_le n S.card)) (zeroMasked S A) j, h j⟩
      inj' := fun _ _ he => (pivotOrder (hm.trans (Nat.sub_le n S.card))
        (zeroMasked S A)).injective (congrArg Subtype.val he) }
  else fallbackOrder S hm

def candidateLabels {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card) (A : Mat n) :
    Fin m ↪ Fin n := (candidateOrder S hm A).trans ⟨Subtype.val, Subtype.val_injective⟩

theorem candidateLabels_avoids {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (A : Mat n) (j : Fin m) : candidateLabels S hm A j ∉ S := (candidateOrder S hm A j).property

theorem measurable_masked_prefix_avoidance {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n) :
    MeasurableSet {A : Mat n | ∀ j : Fin m, pivotOrder hm (zeroMasked S A) j ∉ S} := by
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  have hS : MeasurableSet (S : Set (Fin n)) := S.measurableSet
  exact hS.compl.preimage ((measurable_pivotOrder_coordinate hm j).comp (measurable_zeroMasked S))

theorem measurable_candidateLabels_coordinate {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (j : Fin m) : Measurable (fun A : Mat n => candidateLabels S hm A j) := by
  classical
  have he : (fun A : Mat n => candidateLabels S hm A j) =
      (fun A => if ∀ k : Fin m, pivotOrder (hm.trans (Nat.sub_le n S.card)) (zeroMasked S A) k ∉ S
        then pivotOrder (hm.trans (Nat.sub_le n S.card)) (zeroMasked S A) j
        else (fallbackOrder S hm j).val) := by
    funext A
    unfold candidateLabels candidateOrder
    split_ifs <;> rfl
  rw [he]
  exact Measurable.ite (measurable_masked_prefix_avoidance S (hm.trans (Nat.sub_le n S.card)))
    ((measurable_pivotOrder_coordinate _ j).comp (measurable_zeroMasked S)) measurable_const

theorem measurable_candidateOrder_coordinate {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (j : Fin m) : Measurable (fun A : Mat n => candidateOrder S hm A j) :=
  (measurable_candidateLabels_coordinate S hm j).subtype_mk

theorem candidateOrder_eq_of_outside_eq {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (A B : Mat n) (h : ∀ i : Fin n, i ∉ S → ∀ j : Fin n, A i j = B i j) :
    candidateOrder S hm A = candidateOrder S hm B := by
  unfold candidateOrder
  simp only [zeroMasked_eq_of_outside_eq S A B h]

theorem candidateLabels_eq_of_outside_eq {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (A B : Mat n) (h : ∀ i : Fin n, i ∉ S → ∀ j : Fin n, A i j = B i j) :
    candidateLabels S hm A = candidateLabels S hm B := by
  unfold candidateLabels
  rw [candidateOrder_eq_of_outside_eq S hm A B h]

/-- On an avoiding nonzero actual prefix, the candidate recovers the actual
original pivot labels exactly; its fallback branch is not selected. -/
theorem candidateLabels_eq_actual {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (A : Mat n)
    (havoid : ∀ j : Fin m, pivotOrder (hm.trans (Nat.sub_le n S.card)) A j ∉ S)
    (hnz : ∀ j : Fin m, firstTrajectory A j.val
      (firstPath A (Fin.castLE (hm.trans (Nat.sub_le n S.card)) j))
      (Fin.castLE (hm.trans (Nat.sub_le n S.card)) j) ≠ 0) :
    candidateLabels S hm A = pivotOrder (hm.trans (Nat.sub_le n S.card)) A := by
  have he := pivotOrder_zeroMasked (hm.trans (Nat.sub_le n S.card)) S A havoid hnz
  have hav : ∀ j : Fin m, pivotOrder (hm.trans (Nat.sub_le n S.card)) (zeroMasked S A) j ∉ S := by
    simpa only [he] using havoid
  unfold candidateLabels candidateOrder
  rw [dif_pos hav]
  apply DFunLike.ext
  intro j
  exact congrArg (fun π : Fin m ↪ Fin n => π j) he

theorem candidateLabels_eq_actual_of_nonsingular {n m : ℕ} (S : Finset (Fin n))
    (hm : m ≤ n-S.card) (A : Mat n) (hA : A.det ≠ 0)
    (havoid : ∀ j : Fin m, pivotOrder (hm.trans (Nat.sub_le n S.card)) A j ∉ S) :
    candidateLabels S hm A = pivotOrder (hm.trans (Nat.sub_le n S.card)) A := by
  apply candidateLabels_eq_actual S hm A havoid
  intro j
  have h := (firstPath_admissible_proved A hA (Fin.castLE (hm.trans (Nat.sub_le n S.card)) j)).2.1
  have hv : (Fin.castLE (hm.trans (Nat.sub_le n S.card)) j).val = j.val := rfl
  simpa only [trajectory_firstPath_eq_proved, hv] using h


/-- Only the first m columns of the outside rows influence the candidate. -/
theorem candidateLabels_eq_of_outside_prefix_eq {n m : ℕ} (S : Finset (Fin n))
    (hm : m ≤ n-S.card) (A B : Mat n)
    (h : ∀ i : Fin n, i ∉ S → ∀ j : Fin n, j.val < m → A i j = B i j) :
    candidateLabels S hm A = candidateLabels S hm B := by
  have hp : ColumnsAgree (zeroMasked S A) (zeroMasked S B) m := by
    intro i j hj
    by_cases hi : i ∈ S
    · simp [zeroMasked, maskLabels, hi]
    · simp [zeroMasked, maskLabels, hi, h i hi j hj]
  have he := pivotOrder_columns_congr (hm.trans (Nat.sub_le n S.card))
    (zeroMasked S A) (zeroMasked S B) hp
  unfold candidateLabels candidateOrder
  simp only [he]

/-- Literal outside-row coordinates, used to expose the conditioning map. -/
def outsideData {n : ℕ} (S : Finset (Fin n)) (A : Mat n) : OutsideRows S → Fin n → ℝ :=
  fun i j => A i.val j

def restoreOutside {n : ℕ} (S : Finset (Fin n)) (Z : OutsideRows S → Fin n → ℝ) : Mat n :=
  fun i j => if h : i ∈ S then 0 else Z ⟨i,h⟩ j

theorem measurable_outsideData {n : ℕ} (S : Finset (Fin n)) : Measurable (outsideData S) := by
  unfold outsideData
  fun_prop

theorem measurable_restoreOutside {n : ℕ} (S : Finset (Fin n)) : Measurable (restoreOutside S) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hi : i ∈ S
  · simpa only [restoreOutside, dif_pos hi] using
      (measurable_const : Measurable (fun _ : OutsideRows S → Fin n → ℝ => (0 : ℝ)))
  · simpa only [restoreOutside, dif_neg hi, Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_pi_apply (⟨i,hi⟩ : OutsideRows S))

theorem candidateLabels_outsideData {n m : ℕ} (S : Finset (Fin n)) (hm : m ≤ n-S.card)
    (A : Mat n) :
    candidateLabels S hm A = candidateLabels S hm (restoreOutside S (outsideData S A)) := by
  apply candidateLabels_eq_of_outside_eq
  intro i hi j
  simp only [restoreOutside, dif_neg hi, outsideData]

theorem measurable_candidate_from_outside_coordinate {n m : ℕ} (S : Finset (Fin n))
    (hm : m ≤ n-S.card) (j : Fin m) :
    Measurable (fun Z : OutsideRows S → Fin n → ℝ => candidateLabels S hm (restoreOutside S Z) j) :=
  (measurable_candidateLabels_coordinate S hm j).comp (measurable_restoreOutside S)


/-! Individual transitive kernel audits of all owned declarations. -/
#assert_trust kernel maskLabels
#assert_trust kernel zeroMasked
#assert_trust kernel measurable_zeroMasked
#assert_trust kernel zeroMasked_eq_of_outside_eq
#assert_trust kernel maskLabels_schurStep
#assert_trust kernel firstPivotIndex_maskLabels
#assert_trust kernel firstTrajectory_zeroMasked
#assert_trust kernel firstPath_zeroMasked_prefix
#assert_trust kernel pivotOrder_zeroMasked
#assert_trust kernel OutsideRows
#assert_trust kernel outsideRows_card
#assert_trust kernel fallbackOrder
#assert_trust kernel candidateOrder
#assert_trust kernel candidateLabels
#assert_trust kernel candidateLabels_avoids
#assert_trust kernel measurable_masked_prefix_avoidance
#assert_trust kernel measurable_candidateLabels_coordinate
#assert_trust kernel measurable_candidateOrder_coordinate
#assert_trust kernel candidateOrder_eq_of_outside_eq
#assert_trust kernel candidateLabels_eq_of_outside_eq
#assert_trust kernel candidateLabels_eq_actual
#assert_trust kernel candidateLabels_eq_actual_of_nonsingular
#assert_trust kernel candidateLabels_eq_of_outside_prefix_eq
#assert_trust kernel outsideData
#assert_trust kernel restoreOutside
#assert_trust kernel measurable_outsideData
#assert_trust kernel measurable_restoreOutside
#assert_trust kernel candidateLabels_outsideData
#assert_trust kernel measurable_candidate_from_outside_coordinate

#print axioms maskLabels
#print axioms zeroMasked
#print axioms measurable_zeroMasked
#print axioms zeroMasked_eq_of_outside_eq
#print axioms maskLabels_schurStep
#print axioms firstPivotIndex_maskLabels
#print axioms firstTrajectory_zeroMasked
#print axioms firstPath_zeroMasked_prefix
#print axioms pivotOrder_zeroMasked
#print axioms OutsideRows
#print axioms outsideRows_card
#print axioms fallbackOrder
#print axioms candidateOrder
#print axioms candidateLabels
#print axioms candidateLabels_avoids
#print axioms measurable_masked_prefix_avoidance
#print axioms measurable_candidateLabels_coordinate
#print axioms measurable_candidateOrder_coordinate
#print axioms candidateOrder_eq_of_outside_eq
#print axioms candidateLabels_eq_of_outside_eq
#print axioms candidateLabels_eq_actual
#print axioms candidateLabels_eq_actual_of_nonsingular
#print axioms candidateLabels_eq_of_outside_prefix_eq
#print axioms outsideData
#print axioms restoreOutside
#print axioms measurable_outsideData
#print axioms measurable_restoreOutside
#print axioms candidateLabels_outsideData
#print axioms measurable_candidate_from_outside_coordinate

end NLA.IE06.GaussianPivotMasking
