/-
Canonical pivot filtration and fresh-column laws. New proofs against the exact
credited IE-06 scan and elimination definitions; no arbitrary selector premise.
Preimplementation approval: reviews/pivot-filtration-specification.md.
-/
import NLA.IE06.Pivot
import NLA.IE06.Elimination
import NLA.IE06.Measurability
import NLA.IE06.GaussianNull
import NLA.IE06.Semantics

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace NLA.IE06.PivotFiltration

/-- Original columns revealed before stage k; other entries are set to zero. -/
def pastMatrix {n : ℕ} (k : ℕ) (A : Mat n) : Mat n :=
  fun i j => if j.val < k then A i j else 0

def column {n : ℕ} (j : Fin n) (A : Mat n) : Fin n → ℝ := fun i => A i j

def selectedRows {n : ℕ} (A : Mat n) (k : ℕ) : Mat n :=
  eliminationRows A (firstPath A) k

theorem firstPivotIndex_column_congr {n : ℕ} (S T : Mat n) (k : Fin n)
    (h : ∀ i, S i k = T i k) : firstPivotIndex S k = firstPivotIndex T k := by
  unfold firstPivotIndex
  simp_rw [h]

theorem firstTrajectory_columns_congr {n : ℕ} (A B : Mat n) (d : ℕ)
    (hAB : ColumnsAgree A B d) (s : ℕ) (hs : s ≤ d) :
    ColumnsAgree (firstTrajectory A s) (firstTrajectory B s) d := by
  induction s with
  | zero => exact hAB
  | succ s ih =>
      have hprev := ih (by omega)
      by_cases hsn : s < n
      · have hp : firstPivotIndex (firstTrajectory A s) ⟨s,hsn⟩ =
            firstPivotIndex (firstTrajectory B s) ⟨s,hsn⟩ :=
          firstPivotIndex_column_congr _ _ _ (fun i => hprev i ⟨s,hsn⟩ (by change s < d; omega))
        intro i j hj
        rw [firstTrajectory, firstTrajectory, dif_pos hsn, dif_pos hsn, hp]
        simp only [schurStep, rowSwap]
        rw [hprev _ j hj, hprev _ ⟨s,hsn⟩ (by change s < d; omega),
          hprev _ ⟨s,hsn⟩ (by change s < d; omega), hprev _ j hj]
      · simp only [firstTrajectory, dif_neg hsn]
        exact fun _ _ _ => rfl

theorem firstPath_prefix_congr {n : ℕ} (A B : Mat n) (d : ℕ)
    (hAB : ColumnsAgree A B d) (s : Fin n) (hs : s.val < d) :
    firstPath A s = firstPath B s := by
  exact firstPivotIndex_column_congr _ _ s
    (fun i => firstTrajectory_columns_congr A B d hAB s.val hs.le i s hs)

theorem selectedRows_columns_congr {n : ℕ} (A B : Mat n) (d : ℕ)
    (hAB : ColumnsAgree A B d) (s : ℕ) (hs : s ≤ d) :
    selectedRows A s = selectedRows B s := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hprev := ih (by omega)
      by_cases hsn : s < n
      · have hp := firstPath_prefix_congr A B d hAB ⟨s,hsn⟩ (by change s < d; omega)
        have hc := firstTrajectory_columns_congr A B d hAB s (by omega)
        unfold selectedRows at hprev ⊢
        rw [eliminationRows, eliminationRows, dif_pos hsn, dif_pos hsn, hprev, hp,
          trajectory_firstPath_eq_proved, trajectory_firstPath_eq_proved]
        funext i j
        simp only [eliminationStep, rowSwap]
        rw [hc _ ⟨s,hsn⟩ (by change s < d; omega), hc _ ⟨s,hsn⟩ (by change s < d; omega)]
      · simp only [selectedRows, eliminationRows, dif_neg hsn]

theorem selectedRows_pastMatrix {n : ℕ} (A : Mat n) (k : ℕ) :
    selectedRows A k = selectedRows (pastMatrix k A) k := by
  apply selectedRows_columns_congr A (pastMatrix k A) k _ k le_rfl
  intro i j hj
  simp only [pastMatrix, hj, if_true]

theorem measurable_pastMatrix {n : ℕ} (k : ℕ) : Measurable (@pastMatrix n k) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hj : j.val < k
  · simpa only [pastMatrix, hj, if_true] using measurable_matrix_entry (n := n) i j
  · simpa only [pastMatrix, hj, if_false] using
      (measurable_const : Measurable (fun _ : Mat n => (0 : ℝ)))

theorem measurable_column {n : ℕ} (j : Fin n) : Measurable (@column n j) :=
  measurable_pi_iff.mpr fun i => measurable_matrix_entry i j

private theorem measurable_selected_entry {n : ℕ} {α : Type*} [MeasurableSpace α]
    (S : α → Mat n) (p : α → Fin n) (j : Fin n) (hS : Measurable S) (hp : Measurable p) :
    Measurable (fun a => S a (p a) j) := by
  have hh : Measurable (fun z : Mat n × Fin n => z.1 z.2 j) :=
    measurable_from_prod_countable_left (fun i => measurable_matrix_entry i j)
  exact hh.comp (hS.prodMk hp)

theorem measurable_firstPivotIndex {n : ℕ} (k : Fin n) :
    Measurable (fun S : Mat n => firstPivotIndex S k) := by
  classical
  have hfold (l : List (Fin n)) (p : Mat n → Fin n) (hp : Measurable p) :
      Measurable (fun S => l.foldl
        (fun q i => if k ≤ i ∧ |S q k| < |S i k| then i else q) (p S)) := by
    induction l generalizing p with
    | nil => exact hp
    | cons i l ih =>
        apply ih
        apply Measurable.ite _ measurable_const hp
        by_cases hi : k ≤ i
        · simpa only [hi, true_and, id_eq] using
            measurableSet_lt (measurable_selected_entry id p k measurable_id hp).abs
              (measurable_matrix_entry i k).abs
        · simp [hi]
  exact hfold (List.finRange n) (fun _ => k) measurable_const

theorem measurable_firstTrajectory {n : ℕ} (s : ℕ) :
    Measurable (fun A : Mat n => firstTrajectory A s) := by
  induction s with
  | zero => exact measurable_id
  | succ s ih =>
      by_cases hsn : s < n
      · have hm : Measurable (fun z : Mat n × Fin n => schurStep z.1 ⟨s,hsn⟩ z.2) :=
          measurable_from_prod_countable_left fun p => measurable_schur_fixed ⟨s,hsn⟩ p
        convert hm.comp (ih.prodMk ((measurable_firstPivotIndex ⟨s,hsn⟩).comp ih)) using 1
        funext A
        rw [firstTrajectory, dif_pos hsn]
        rfl
      · simpa only [firstTrajectory, dif_neg hsn] using
          (measurable_const : Measurable (fun _ : Mat n => (0 : Mat n)))

theorem measurable_firstPath (n : ℕ) : Measurable (@firstPath n) :=
  measurable_pi_iff.mpr fun k => (measurable_firstPivotIndex k).comp
    (measurable_firstTrajectory k.val)

private theorem measurable_eliminationStep_fixed {n : ℕ} (k p : Fin n) :
    Measurable (fun z : Mat n × Mat n => eliminationStep z.1 z.2 k p) := by
  apply measurable_matrix_entries
  intro i j
  by_cases hi : k < i
  · simp only [eliminationStep, rowSwap, hi, if_true]
    fun_prop
  · simp only [eliminationStep, rowSwap, hi, if_false]
    exact measurable_const

theorem measurable_eliminationRows_fixed {n : ℕ} (path : PivotPath n) (s : ℕ) :
    Measurable (fun A : Mat n => eliminationRows A path s) := by
  induction s with
  | zero => exact measurable_const
  | succ s ih =>
      by_cases hsn : s < n
      · convert (measurable_eliminationStep_fixed ⟨s,hsn⟩ (path ⟨s,hsn⟩)).comp
          ((measurable_trajectory_fixed path s).prodMk ih) using 1
        funext A
        rw [eliminationRows, dif_pos hsn]
        rfl
      · simpa only [eliminationRows, dif_neg hsn] using
          (measurable_const : Measurable (fun _ : Mat n => (0 : Mat n)))

theorem measurable_selectedRows {n : ℕ} (s : ℕ) :
    Measurable (fun A : Mat n => selectedRows A s) := by
  have hm : Measurable (fun z : Mat n × PivotPath n => eliminationRows z.1 z.2 s) :=
    measurable_from_prod_countable_left fun path => measurable_eliminationRows_fixed path s
  exact hm.comp (measurable_id.prodMk (measurable_firstPath n))

/-- Rearranging the literal iid entries into columns preserves the iid law. -/
theorem gaussian_columns_map (n : ℕ) :
    (gaussianMatrix n).map (fun A : Mat n => fun j i => A i j) =
      GaussianNull.gaussianRect n n := by
  let e := (MeasurableEquiv.curry (Fin n) (Fin n) ℝ).symm
  apply (e.measurableEmbedding.map_injective)
  have ht : Measurable (fun A : Mat n => fun j i => A i j) := by fun_prop
  rw [Measure.map_map e.measurable ht]
  have hright := GaussianNull.gaussian_uncurry_map n n
  change Measure.map (fun A : Mat n => fun ij : Fin n × Fin n => A ij.2 ij.1)
    (gaussianMatrix n) = _
  change _ = Measure.map Function.uncurry (GaussianNull.gaussianRect n n)
  rw [hright]
  let q := MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin n => ℝ)
    (Equiv.prodComm (Fin n) (Fin n))
  have hq : (fun A : Mat n => fun ij : Fin n × Fin n => A ij.2 ij.1) =
      q ∘ Function.uncurry := by rfl
  rw [hq]
  change Measure.map (q ∘ Function.uncurry) (GaussianNull.gaussianRect n n) = _
  rw [← Measure.map_map q.measurable measurable_uncurry]
  change Measure.map q (Measure.map Function.uncurry (GaussianNull.gaussianRect n n)) = _
  rw [GaussianNull.gaussian_uncurry_map]
  exact Measure.pi_map_piCongrLeft (Equiv.prodComm (Fin n) (Fin n))
    (fun _ => gaussianReal 0 1)

theorem gaussian_column_map {n : ℕ} (j : Fin n) :
    (gaussianMatrix n).map (column j) =
      Measure.pi (fun _ : Fin n => gaussianReal 0 1) := by
  have hm := measurePreserving_eval (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => gaussianReal 0 1)) j
  change MeasurePreserving (Function.eval j) (GaussianNull.gaussianRect n n) _ at hm
  rw [← gaussian_columns_map n] at hm
  have hh := hm.map_eq
  rw [Measure.map_map (measurable_pi_apply j) (by fun_prop)] at hh
  exact hh

theorem gaussian_columns_independent (n : ℕ) :
    iIndepFun (fun j : Fin n => column j) (gaussianMatrix n) := by
  let : IsProbabilityMeasure (gaussianMatrix n) := gaussianMatrix_probability_proved n
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_column j).aemeasurable)).2
  simp_rw [gaussian_column_map]
  exact gaussian_columns_map n

theorem pastMatrix_independent_column {n : ℕ} (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    IndepFun (pastMatrix k) (column j) (gaussianMatrix n) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun a => a.val < k)
  let T : Finset (Fin n) := {j}
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro a ha hat
    have haj : a = j := by simpa [T] using hat
    subst a
    have hjk : j.val < k := (Finset.mem_filter.mp ha).2
    omega
  have hi := iIndepFun.indepFun_finset S T hd (gaussian_columns_independent n)
    (fun a => measurable_column a)
  let restore : (S → Fin n → ℝ) → Mat n := fun z i a =>
    if h : a ∈ S then z ⟨a,h⟩ i else 0
  have hr : Measurable restore := by
    apply measurable_matrix_entries
    intro i a
    by_cases ha : a ∈ S
    · simpa only [restore, dif_pos ha, Function.comp_def] using
        (measurable_pi_apply i).comp (measurable_pi_apply (⟨a,ha⟩ : S))
    · simpa only [restore, dif_neg ha] using
        (measurable_const : Measurable (fun _ : S → Fin n → ℝ => (0 : ℝ)))
  have he := hi.comp hr (measurable_pi_apply (⟨j,by simp [T]⟩ : T))
  convert he using 1
  · funext A i a
    change (if a.val < k then A i a else 0) =
      (if h : a ∈ S then (fun b : S => column b.val A) ⟨a,h⟩ i else 0)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, column]
    split_ifs <;> rfl
  · rfl

theorem selectedRows_independent_column {n : ℕ} (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    IndepFun (fun A : Mat n => selectedRows A k) (column j) (gaussianMatrix n) := by
  have h := (pastMatrix_independent_column k j hj).comp (measurable_selectedRows k) measurable_id
  convert h using 1
  · funext A
    exact selectedRows_pastMatrix A k
  · rfl

theorem selectedRows_column_joint_law {n : ℕ} (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    (gaussianMatrix n).map (fun A : Mat n => (selectedRows A k, column j A)) =
      ((gaussianMatrix n).map (fun A : Mat n => selectedRows A k)).prod
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  let : IsProbabilityMeasure (gaussianMatrix n) := gaussianMatrix_probability_proved n
  have h := (selectedRows_independent_column k j hj).map_prod_eq_prod_map_map
    (measurable_selectedRows k).aemeasurable (measurable_column j).aemeasurable
  rwa [gaussian_column_map] at h

/-- The whole unrevealed block, indexed by its original column labels. -/
def futureColumns {n : ℕ} (k : ℕ) (A : Mat n) :
    {j : Fin n // k ≤ j.val} → Fin n → ℝ := fun j => column j.val A

theorem measurable_futureColumns {n : ℕ} (k : ℕ) :
    Measurable (@futureColumns n k) :=
  measurable_pi_iff.mpr fun j => measurable_column j.val

theorem gaussian_futureColumns_map {n : ℕ} (k : ℕ) :
    (gaussianMatrix n).map (futureColumns k) =
      Measure.pi (fun _ : {j : Fin n // k ≤ j.val} =>
        Measure.pi (fun _ : Fin n => gaussianReal 0 1)) := by
  have hi : iIndepFun (fun j : {j : Fin n // k ≤ j.val} => column j.val)
      (gaussianMatrix n) :=
    (gaussian_columns_independent n).precomp Subtype.val_injective
  have hm := hi.map_fun_eq_pi_map
    (fun j : {j : Fin n // k ≤ j.val} => (measurable_column j.val).aemeasurable)
  change (gaussianMatrix n).map
    (fun A : Mat n => fun j : {j : Fin n // k ≤ j.val} => column j.val A) = _
  simpa only [gaussian_column_map] using hm

theorem pastMatrix_independent_futureColumns {n : ℕ} (k : ℕ) :
    IndepFun (pastMatrix k) (futureColumns k) (gaussianMatrix n) := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun a => a.val < k)
  let T : Finset (Fin n) := Finset.univ.filter (fun a => k ≤ a.val)
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro a ha hat
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hat).2
    omega
  have hi := iIndepFun.indepFun_finset S T hd (gaussian_columns_independent n)
    (fun a => measurable_column a)
  let restore : (S → Fin n → ℝ) → Mat n := fun z i a =>
    if h : a ∈ S then z ⟨a,h⟩ i else 0
  have hr : Measurable restore := by
    apply measurable_matrix_entries
    intro i a
    by_cases ha : a ∈ S
    · simpa only [restore, dif_pos ha, Function.comp_def] using
        (measurable_pi_apply i).comp (measurable_pi_apply (⟨a,ha⟩ : S))
    · simpa only [restore, dif_neg ha] using
        (measurable_const : Measurable (fun _ : S → Fin n → ℝ => (0 : ℝ)))
  let collect : (T → Fin n → ℝ) → ({j : Fin n // k ≤ j.val} → Fin n → ℝ) :=
    fun z j => z ⟨j.val, by simp [T, j.property]⟩
  have hc : Measurable collect := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_pi_apply _
  have he := hi.comp hr hc
  convert he using 1
  · funext A i a
    change (if a.val < k then A i a else 0) =
      (if h : a ∈ S then (fun b : S => column b.val A) ⟨a,h⟩ i else 0)
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, column]
    split_ifs <;> rfl
  · rfl

theorem selectedRows_independent_futureColumns {n : ℕ} (k : ℕ) :
    IndepFun (fun A : Mat n => selectedRows A k) (futureColumns k) (gaussianMatrix n) := by
  have h := (pastMatrix_independent_futureColumns (n := n) k).comp
    (measurable_selectedRows k) measurable_id
  convert h using 1
  · funext A
    exact selectedRows_pastMatrix A k
  · rfl

theorem selectedRows_futureColumns_joint_law {n : ℕ} (k : ℕ) :
    (gaussianMatrix n).map (fun A : Mat n => (selectedRows A k, futureColumns k A)) =
      ((gaussianMatrix n).map (fun A : Mat n => selectedRows A k)).prod
        (Measure.pi (fun _ : {j : Fin n // k ≤ j.val} =>
          Measure.pi (fun _ : Fin n => gaussianReal 0 1))) := by
  let : IsProbabilityMeasure (gaussianMatrix n) := gaussianMatrix_probability_proved n
  have h := (selectedRows_independent_futureColumns (n := n) k).map_prod_eq_prod_map_map
    (measurable_selectedRows k).aemeasurable (measurable_futureColumns k).aemeasurable
  rwa [gaussian_futureColumns_map] at h

#assert_trust kernel pastMatrix
#print axioms pastMatrix
#assert_trust kernel column
#print axioms column
#assert_trust kernel selectedRows
#print axioms selectedRows
#assert_trust kernel firstPivotIndex_column_congr
#print axioms firstPivotIndex_column_congr
#assert_trust kernel firstTrajectory_columns_congr
#print axioms firstTrajectory_columns_congr
#assert_trust kernel firstPath_prefix_congr
#print axioms firstPath_prefix_congr
#assert_trust kernel selectedRows_columns_congr
#print axioms selectedRows_columns_congr
#assert_trust kernel selectedRows_pastMatrix
#print axioms selectedRows_pastMatrix
#assert_trust kernel measurable_pastMatrix
#print axioms measurable_pastMatrix
#assert_trust kernel measurable_column
#print axioms measurable_column
#assert_trust kernel measurable_selected_entry
#print axioms measurable_selected_entry
#assert_trust kernel measurable_firstPivotIndex
#print axioms measurable_firstPivotIndex
#assert_trust kernel measurable_firstTrajectory
#print axioms measurable_firstTrajectory
#assert_trust kernel measurable_firstPath
#print axioms measurable_firstPath
#assert_trust kernel measurable_eliminationStep_fixed
#print axioms measurable_eliminationStep_fixed
#assert_trust kernel measurable_eliminationRows_fixed
#print axioms measurable_eliminationRows_fixed
#assert_trust kernel measurable_selectedRows
#print axioms measurable_selectedRows
#assert_trust kernel gaussian_columns_map
#print axioms gaussian_columns_map
#assert_trust kernel gaussian_column_map
#print axioms gaussian_column_map
#assert_trust kernel gaussian_columns_independent
#print axioms gaussian_columns_independent
#assert_trust kernel pastMatrix_independent_column
#print axioms pastMatrix_independent_column
#assert_trust kernel selectedRows_independent_column
#print axioms selectedRows_independent_column
#assert_trust kernel selectedRows_column_joint_law
#print axioms selectedRows_column_joint_law
#assert_trust kernel futureColumns
#print axioms futureColumns
#assert_trust kernel measurable_futureColumns
#print axioms measurable_futureColumns
#assert_trust kernel gaussian_futureColumns_map
#print axioms gaussian_futureColumns_map
#assert_trust kernel pastMatrix_independent_futureColumns
#print axioms pastMatrix_independent_futureColumns
#assert_trust kernel selectedRows_independent_futureColumns
#print axioms selectedRows_independent_futureColumns
#assert_trust kernel selectedRows_futureColumns_joint_law
#print axioms selectedRows_futureColumns_joint_law

end NLA.IE06.PivotFiltration
