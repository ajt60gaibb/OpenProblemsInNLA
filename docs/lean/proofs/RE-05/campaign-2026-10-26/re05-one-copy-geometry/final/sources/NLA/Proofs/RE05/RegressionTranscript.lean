import NLA.Statements.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix

/-- Exact finite-list slice, allowing arbitrary and zero block lengths. -/
theorem finRange_flatMap_slice {α : Type*} {m : ℕ} (f : Fin m → List α) (j : Fin m) :
    (((List.finRange m).flatMap f).drop
      (∑ i : Fin m, if i < j then (f i).length else 0)).take (f j).length = f j := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [List.finRange_succ, List.flatMap_map]
    · have hoff : (∑ i : Fin (m + 1), if i < k.succ then (f i).length else 0) =
        (f 0).length + ∑ i : Fin m, if i < k then (f i.succ).length else 0 := by
        rw [Fin.sum_univ_succ]
        simp
      rw [List.finRange_succ, List.flatMap_cons, List.flatMap_map, hoff,
        ← List.drop_drop, List.drop_left]
      exact ih (fun i => f i.succ) k

/-- One plan's actual oracle responses, in the model's left/right order. -/
def planAnswers {n : ℕ} (A : Square n) (plan : Plan n) : List (Fin n → ℝ) :=
  (queries plan).map (NLA.Computation.NonadaptiveMatrixQuery.answer A)

theorem copyResponses_batchAnswers {n : ℕ} (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) :
    copyResponses schedule (batchAnswers A schedule) copy = planAnswers A (schedule copy) := by
  unfold copyResponses batchAnswers batchQueries responseOffset planAnswers
  rw [List.map_flatMap]
  simpa only [List.length_map] using
    finRange_flatMap_slice (fun c : Fin 15 =>
      (queries (schedule c)).map (NLA.Computation.NonadaptiveMatrixQuery.answer A)) copy

theorem planAnswers_layout {n : ℕ} (A : Square n) (plan : Plan n) :
    planAnswers A plan =
      plan.selected.map (fun h => fun k => ∑ i : Fin n, A i k * plan.U i h) ++
        (List.finRange plan.s).map (fun g => fun i => ∑ k : Fin n, A i k * plan.G k g) := by
  simp [planAnswers, queries, List.map_map, Function.comp_def,
    NLA.Computation.NonadaptiveMatrixQuery.answer]

theorem storedVector_append_left {n : ℕ} (xs ys : List (Fin n → ℝ)) (j : ℕ)
    (hj : j < xs.length) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs ++ ys) j =
      NLA.Computation.NonadaptiveMatrixQuery.storedVector xs j := by
  unfold NLA.Computation.NonadaptiveMatrixQuery.storedVector
  rw [List.getElem?_append_left hj]

theorem storedVector_append_right {n : ℕ} (xs ys : List (Fin n → ℝ)) (j : ℕ) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs ++ ys) (xs.length + j) =
      NLA.Computation.NonadaptiveMatrixQuery.storedVector ys j := by
  unfold NLA.Computation.NonadaptiveMatrixQuery.storedVector
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]

theorem storedVector_map_get {α : Type*} {n : ℕ} (xs : List α)
    (f : α → Fin n → ℝ) (j : Fin xs.length) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs.map f) j.val = f xs[j] := by
  simp [NLA.Computation.NonadaptiveMatrixQuery.storedVector]

theorem observedLeft_planAnswers {n : ℕ} (A : Square n) (plan : Plan n)
    (h : Fin plan.selected.length) :
    observedLeft plan (planAnswers A plan) h = A.transpose *ᵥ uColumn plan h := by
  unfold observedLeft
  rw [planAnswers_layout, storedVector_append_left _ _ _ (by simp), storedVector_map_get]
  rfl

theorem observedRight_planAnswers {n : ℕ} (A : Square n) (plan : Plan n)
    (g : Fin plan.s) :
    observedRight plan (planAnswers A plan) g = A *ᵥ (fun k => plan.G k g) := by
  unfold observedRight
  rw [planAnswers_layout]
  have h := storedVector_append_right
    (plan.selected.map (fun h => fun k => ∑ i : Fin n, A i k * plan.U i h))
    ((List.finRange plan.s).map (fun g => fun i => ∑ k : Fin n, A i k * plan.G k g)) g.val
  simp only [List.length_map] at h
  rw [h]
  simp [NLA.Computation.NonadaptiveMatrixQuery.storedVector]
  rfl

theorem observedLeft_copyResponses {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) (h : Fin (schedule copy).selected.length) :
    observedLeft (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) h =
      A.transpose *ᵥ uColumn (schedule copy) h := by
  rw [copyResponses_batchAnswers, observedLeft_planAnswers]

theorem observedRight_copyResponses {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) (g : Fin (schedule copy).s) :
    observedRight (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) g =
      A *ᵥ (fun k => (schedule copy).G k g) := by
  rw [copyResponses_batchAnswers, observedRight_planAnswers]

end NLA.Proofs.RE05
