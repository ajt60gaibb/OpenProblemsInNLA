import NLA.Proofs.SP11.GreedyRelabel
import Mathlib.Data.List.Sort

/-!
# Strict sibling labels and the actual greedy arity bounds

The sorted predecessor lists have strictly increasing labels. The augmented
list inserts one earlier adjacent root, which is absent from the nonneighbor
list. These facts expose the actual child-position inequalities needed for
canonical garden colors; they do not assert polynomial noncancellation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- In a strictly sorted list, exactly the earlier slots have smaller values. -/
theorem sortedLT_filter_lt_length {α : Type*} [LinearOrder α]
    (l : List α) (h : l.SortedLT) (s : Fin l.length) :
    (l.filter (fun w => decide (w < l.get s))).length = s.val := by
  classical
  rw [← List.toFinset_card_of_nodup (h.nodup.filter (fun w => decide (w < l.get s)))]
  have hset : (l.filter (fun w => decide (w < l.get s))).toFinset =
      (Finset.Iio s).image l.get := by
    ext w
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      Finset.mem_image, Finset.mem_Iio]
    constructor
    · rintro ⟨hw, hlt⟩
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp hw
      exact ⟨r, h.strictMono_get.lt_iff_lt.mp (by simpa only [hr] using hlt), hr⟩
    · rintro ⟨r, hr, rfl⟩
      exact ⟨List.get_mem l r, h.strictMono_get hr⟩
  rw [hset, Finset.card_image_of_injective _ h.strictMono_get.injective]
  simp

theorem priorNonneighbors_sortedLT {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    (priorNonneighbors G j).SortedLT := by
  classical
  exact Finset.sortedLT_sort _

/-- Earlier child slots have strictly earlier vertex labels. -/
theorem priorVertex_strictMono {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    StrictMono (priorVertex G j) :=
  (priorNonneighbors_sortedLT G j).strictMono_get

theorem priorVertex_label_lt_parent {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) : priorVertex G j s < j :=
  priorVertex_lt G j s

theorem priorNonneighbors_count_lt_priorVertex {n : ℕ}
    (G : SimpleGraph (Fin n)) (j : Fin n) (s : Fin (priorNonneighbors G j).length) :
    ((priorNonneighbors G j).filter (fun w => decide (w < priorVertex G j s))).length =
      s.val :=
  sortedLT_filter_lt_length _ (priorNonneighbors_sortedLT G j) s

/-- A child's own input arity is at most its zero-based sibling slot. -/
theorem OrderedGreedy.priorVertex_arity_le_slot {n : ℕ}
    (G : SimpleGraph (Fin n)) (hgr : OrderedGreedy G) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) :
    (priorNonneighbors G (priorVertex G j s)).length ≤ s.val := by
  have h := OrderedGreedy.prior_length_lt_insertionPosition G hgr
    (priorVertex G j s) j (priorVertex_label_lt_parent G j s).le
  rw [priorNonneighbors_count_lt_priorVertex] at h
  omega

/-- Insert the earlier root into the actual ordered nonneighbor children. -/
noncomputable def augmentedPriorNonneighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (j i : Fin n) : List (Fin n) := by
  classical
  exact (insert i (priorNonneighbors G j).toFinset).sort (· ≤ ·)

theorem mem_augmentedPriorNonneighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (j i v : Fin n) :
    v ∈ augmentedPriorNonneighbors G j i ↔ v = i ∨ v < j ∧ ¬ G.Adj j v := by
  classical
  simp [augmentedPriorNonneighbors, mem_priorNonneighbors]

/-- The edge hypothesis excludes a duplicate of the earlier top-root label. -/
theorem adjacent_not_mem_priorNonneighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) : i ∉ priorNonneighbors G j := by
  intro hmem
  exact ((mem_priorNonneighbors G i j).mp hmem).2 hij.symm

theorem augmentedPriorNonneighbors_sortedLT {n : ℕ} (G : SimpleGraph (Fin n))
    (j i : Fin n) : (augmentedPriorNonneighbors G j i).SortedLT := by
  classical
  exact Finset.sortedLT_sort _

theorem augmentedPriorNonneighbors_length {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) :
    (augmentedPriorNonneighbors G j i).length = (priorNonneighbors G j).length + 1 := by
  classical
  have hnot : i ∉ (priorNonneighbors G j).toFinset := by
    simpa using adjacent_not_mem_priorNonneighbors G i j hij
  simp only [augmentedPriorNonneighbors, Finset.length_sort,
    Finset.card_insert_of_notMem hnot,
    List.toFinset_card_of_nodup (priorNonneighbors_sortedLT G j).nodup]

noncomputable def augmentedPriorVertex {n : ℕ} (G : SimpleGraph (Fin n))
    (j i : Fin n) (s : Fin (augmentedPriorNonneighbors G j i).length) : Fin n :=
  (augmentedPriorNonneighbors G j i).get s

theorem augmentedPriorVertex_strictMono {n : ℕ} (G : SimpleGraph (Fin n))
    (j i : Fin n) : StrictMono (augmentedPriorVertex G j i) :=
  (augmentedPriorNonneighbors_sortedLT G j i).strictMono_get

theorem augmentedPriorVertex_label_lt_parent {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i < j)
    (s : Fin (augmentedPriorNonneighbors G j i).length) :
    augmentedPriorVertex G j i s < j := by
  have hmem := (mem_augmentedPriorNonneighbors G j i _).mp
    (List.get_mem (augmentedPriorNonneighbors G j i) s)
  rcases hmem with heq | hmem
  · change (augmentedPriorNonneighbors G j i).get s < j
    rw [heq]
    exact hij
  · exact hmem.1

theorem augmentedPriorNonneighbors_count_lt_vertex {n : ℕ}
    (G : SimpleGraph (Fin n)) (j i : Fin n)
    (s : Fin (augmentedPriorNonneighbors G j i).length) :
    ((augmentedPriorNonneighbors G j i).filter
      (fun w => decide (w < augmentedPriorVertex G j i s))).length = s.val :=
  sortedLT_filter_lt_length _ (augmentedPriorNonneighbors_sortedLT G j i) s

/-- Inserting one root cannot decrease the count of earlier ordinary children. -/
theorem prior_filter_length_le_augmented {n : ℕ} (G : SimpleGraph (Fin n))
    (j i v : Fin n) :
    ((priorNonneighbors G j).filter (fun w => decide (w < v))).length ≤
      ((augmentedPriorNonneighbors G j i).filter (fun w => decide (w < v))).length := by
  classical
  rw [← List.toFinset_card_of_nodup ((priorNonneighbors_sortedLT G j).nodup.filter _),
    ← List.toFinset_card_of_nodup ((augmentedPriorNonneighbors_sortedLT G j i).nodup.filter _)]
  apply Finset.card_le_card
  intro w hw
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hw ⊢
  exact ⟨(mem_augmentedPriorNonneighbors G j i w).mpr
    (Or.inr ((mem_priorNonneighbors G w j).mp hw.1)), hw.2⟩

/-- Every augmented child, including the earlier adjacent root, has own arity
at most its zero-based augmented slot. No distinct-occurrence assumption is used. -/
theorem OrderedGreedy.augmentedPriorVertex_arity_le_slot {n : ℕ}
    (G : SimpleGraph (Fin n)) (hgr : OrderedGreedy G) (i j : Fin n) (hij : i < j)
    (s : Fin (augmentedPriorNonneighbors G j i).length) :
    (priorNonneighbors G (augmentedPriorVertex G j i s)).length ≤ s.val := by
  have h := OrderedGreedy.prior_length_lt_insertionPosition G hgr
    (augmentedPriorVertex G j i s) j (augmentedPriorVertex_label_lt_parent G i j hij s).le
  have hc := prior_filter_length_le_augmented G j i (augmentedPriorVertex G j i s)
  rw [augmentedPriorNonneighbors_count_lt_vertex] at hc
  omega

#assert_trust kernel priorVertex_strictMono
#assert_trust kernel OrderedGreedy.priorVertex_arity_le_slot
#assert_trust kernel augmentedPriorVertex_strictMono
#assert_trust kernel augmentedPriorNonneighbors_length
#assert_trust kernel OrderedGreedy.augmentedPriorVertex_arity_le_slot
#print axioms OrderedGreedy.priorVertex_arity_le_slot
#print axioms OrderedGreedy.augmentedPriorVertex_arity_le_slot

end NLA.Proofs.SP11
