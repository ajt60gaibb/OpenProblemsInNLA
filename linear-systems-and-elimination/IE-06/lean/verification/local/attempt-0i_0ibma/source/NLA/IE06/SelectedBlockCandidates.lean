import NLA.IE06.GaussianCandidateStacking
import NLA.IE06.SelectedBlockElimination

/-! The actual next pivot rows are among the fixed outside-only candidates.
Ordered injections index the finite union; their number is at most n^s. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix Set
open scoped ENNReal BigOperators
namespace NLA.IE06.SelectedBlockCandidates
open GaussianPivotConditioning GaussianPivotMasking GaussianCandidateRows
open GaussianCandidateStacking GaussianStackingTail Spectral SpectralMeasurability

def actualBlock {n t : ℕ} (ht : t ≤ n) (A : Mat n) : Mat t :=
  selectedBlock ht (pivotOrder ht A) A

def extendedBlock {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) : GaussianNull.RectMat m (m+s) :=
  fun i j => A (pivotOrder (by omega : m ≤ n) A i) (Fin.castLE hp j)

def nextOrder {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) : Fin s ↪ Fin n :=
  (⟨Fin.natAdd m, Fin.natAdd_injective s m⟩ : Fin s ↪ Fin (m+s)).trans (pivotOrder hp A)

def rowSet {n s : ℕ} (ρ : Fin s ↪ Fin n) : Finset (Fin n) := Finset.univ.map ρ

theorem rowSet_card {n s : ℕ} (ρ : Fin s ↪ Fin n) : (rowSet ρ).card = s := by
  simp [rowSet]

theorem mem_rowSet {n s : ℕ} (ρ : Fin s ↪ Fin n) (i : Fin n) :
    i ∈ rowSet ρ ↔ i ∈ Set.range ρ := by simp [rowSet]

def rowSetEquiv {n s : ℕ} (ρ : Fin s ↪ Fin n) : Fin s ≃ InsideRows (rowSet ρ) :=
  Equiv.ofBijective (fun i => ⟨ρ i, (mem_rowSet ρ (ρ i)).mpr ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => ρ.injective (congrArg Subtype.val h), fun i => by
      obtain ⟨j,hj⟩ := (mem_rowSet ρ i.val).mp i.property
      exact ⟨j,Subtype.ext hj⟩⟩

theorem rowSetEquiv_apply {n s : ℕ} (ρ : Fin s ↪ Fin n) (i : Fin s) :
    (rowSetEquiv ρ i).val = ρ i := rfl

theorem pivotOrder_prefix {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) (i : Fin m) :
    pivotOrder hp A (Fin.castAdd s i) = pivotOrder (by omega : m ≤ n) A i := by
  rw [pivotOrder_stage, pivotOrder_stage]
  rfl

theorem nextOrder_avoids_prefix {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) (i : Fin m) :
    pivotOrder (by omega : m ≤ n) A i ∉ rowSet (nextOrder hp A) := by
  intro h
  obtain ⟨j,hj⟩ := (mem_rowSet _ _).mp h
  have he : pivotOrder hp A (Fin.natAdd m j) = pivotOrder hp A (Fin.castAdd s i) := by
    rw [pivotOrder_prefix]
    exact hj
  have hv := congrArg Fin.val ((pivotOrder hp A).injective he)
  simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

theorem candidateBlock_actual {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) (hA : A.det ≠ 0) :
    candidateBlock (rowSet (nextOrder hp A)) (by rw [rowSet_card]; omega) hp
      (outsideData (rowSet (nextOrder hp A)) A) = extendedBlock hp A := by
  rw [candidateBlock_outsideData]
  have h := candidateLabels_eq_actual_of_nonsingular (rowSet (nextOrder hp A))
    (by rw [rowSet_card]; omega : m ≤ n-(rowSet (nextOrder hp A)).card) A hA
    (nextOrder_avoids_prefix hp A)
  rw [h]
  rfl

theorem stack_actual {n m s : ℕ} (hp : m+s ≤ n) (A : Mat n) :
    Matrix.fromRows (Matrix.of (extendedBlock hp A))
      (Matrix.of (insideData (rowSet (nextOrder hp A)) (rowSetEquiv (nextOrder hp A)) hp A)) =
      (Matrix.of (actualBlock hp A)).submatrix (finSumFinEquiv : Fin m ⊕ Fin s ≃ Fin (m+s)) id := by
  ext i j
  cases i with
  | inl i =>
    change A (pivotOrder (by omega : m ≤ n) A i) (Fin.castLE hp j) =
      A (pivotOrder hp A (Fin.castAdd s i)) (Fin.castLE hp j)
    rw [pivotOrder_prefix]
  | inr i =>
    change A ((rowSetEquiv (nextOrder hp A) i).val) (Fin.castLE hp j) =
      A (pivotOrder hp A (Fin.natAdd m i)) (Fin.castLE hp j)
    rw [rowSetEquiv_apply]
    rfl

def fixedCandidateEvent {n m s : ℕ} (hp : m+s ≤ n) (ρ : Fin s ↪ Fin n)
    (j : ℕ) (a f x θ : ℝ) : Set (Mat n) :=
  {A | (candidateBlock (rowSet ρ) (by rw [rowSet_card]; omega) hp (outsideData (rowSet ρ) A),
    insideData (rowSet ρ) (rowSetEquiv ρ) hp A) ∈ stackBadEvent m s j a f x θ}

theorem fixedCandidateEvent_measure_le {n m s j : ℕ} (hp : m+s ≤ n)
    (ρ : Fin s ↪ Fin n) (hj : 4 ≤ j) (hjs : 2*j < s) (hjm : j < m)
    {a f x θ : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hx : 0 < x)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    gaussianMatrix n (fixedCandidateEvent hp ρ j a f x θ) ≤
      ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4)) :=
  candidate_stacking_tail (rowSet ρ) (rowSetEquiv ρ)
    (by rw [rowSet_card]; omega) hp hj hjs hjm ha hf hx hθ hθone

theorem actual_event_subset_candidates {n m s j : ℕ} (hp : m+s ≤ n) (a f x θ : ℝ) :
    {A : Mat n | A.det ≠ 0 ∧ inverseCap a f (Matrix.of (extendedBlock hp A)) ∧
      singularValue (Matrix.of (actualBlock hp A)) (m+s-2*j-1) ≤ stackingThreshold s j a f x θ} ⊆
      ⋃ ρ : Fin s ↪ Fin n, fixedCandidateEvent hp ρ j a f x θ := by
  intro A hA
  refine Set.mem_iUnion.mpr ⟨nextOrder hp A, ?_⟩
  simp only [fixedCandidateEvent, Set.mem_ofPred_eq, stackBadEvent]
  rw [candidateBlock_actual hp A hA.1]
  refine ⟨hA.2.1, ?_⟩
  rw [stack_actual, singularValue_rowEquiv]
  exact hA.2.2

theorem card_ordered_candidates_le (n s : ℕ) : Fintype.card (Fin s ↪ Fin n) ≤ n^s := by
  have h := Fintype.card_le_of_injective (fun ρ : Fin s ↪ Fin n => (ρ : Fin s → Fin n))
    (fun ρ σ h => DFunLike.ext _ _ (fun i => congrFun h i))
  simpa only [Fintype.card_fun,Fintype.card_fin] using h

theorem actual_stacking_union_tail {n m s j : ℕ} (hp : m+s ≤ n)
    (hj : 4 ≤ j) (hjs : 2*j < s) (hjm : j < m)
    {a f x θ : ℝ} (ha : 0 < a) (hf : 0 ≤ f) (hx : 0 < x)
    (hθ : 0 < θ) (hθone : θ ≤ 1) :
    gaussianMatrix n {A : Mat n | A.det ≠ 0 ∧ inverseCap a f (Matrix.of (extendedBlock hp A)) ∧
      singularValue (Matrix.of (actualBlock hp A)) (m+s-2*j-1) ≤ stackingThreshold s j a f x θ} ≤
      (n:ℝ≥0∞)^s*(ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4))) := by
  calc
    _ ≤ gaussianMatrix n (⋃ ρ : Fin s ↪ Fin n, fixedCandidateEvent hp ρ j a f x θ) :=
      measure_mono (actual_event_subset_candidates hp a f x θ)
    _ ≤ ∑ ρ : Fin s ↪ Fin n, gaussianMatrix n (fixedCandidateEvent hp ρ j a f x θ) :=
      measure_iUnion_fintype_le _ _
    _ ≤ ∑ _ρ : Fin s ↪ Fin n, (ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4))) :=
      Finset.sum_le_sum (fun ρ _ => fixedCandidateEvent_measure_le hp ρ hj hjs hjm ha hf hx hθ hθone)
    _ = (Fintype.card (Fin s ↪ Fin n) : ℝ≥0∞)*(ENNReal.ofReal (Real.exp (-x))+
        ENNReal.ofReal ((s:ℝ)^(j+1)*θ^((j:ℝ)^2/4))) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ _ := by
      gcongr
      exact_mod_cast card_ordered_candidates_le n s

#assert_trust kernel actualBlock
#print axioms actualBlock
#assert_trust kernel extendedBlock
#print axioms extendedBlock
#assert_trust kernel nextOrder
#print axioms nextOrder
#assert_trust kernel rowSet
#print axioms rowSet
#assert_trust kernel rowSet_card
#print axioms rowSet_card
#assert_trust kernel mem_rowSet
#print axioms mem_rowSet
#assert_trust kernel rowSetEquiv
#print axioms rowSetEquiv
#assert_trust kernel rowSetEquiv_apply
#print axioms rowSetEquiv_apply
#assert_trust kernel pivotOrder_prefix
#print axioms pivotOrder_prefix
#assert_trust kernel nextOrder_avoids_prefix
#print axioms nextOrder_avoids_prefix
#assert_trust kernel candidateBlock_actual
#print axioms candidateBlock_actual
#assert_trust kernel stack_actual
#print axioms stack_actual
#assert_trust kernel fixedCandidateEvent
#print axioms fixedCandidateEvent
#assert_trust kernel fixedCandidateEvent_measure_le
#print axioms fixedCandidateEvent_measure_le
#assert_trust kernel actual_event_subset_candidates
#print axioms actual_event_subset_candidates
#assert_trust kernel card_ordered_candidates_le
#print axioms card_ordered_candidates_le
#assert_trust kernel actual_stacking_union_tail
#print axioms actual_stacking_union_tail

end NLA.IE06.SelectedBlockCandidates
