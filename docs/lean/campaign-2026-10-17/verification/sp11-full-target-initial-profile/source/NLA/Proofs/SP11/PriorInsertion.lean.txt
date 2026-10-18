import NLA.Proofs.SP11.PriorListStructure
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Exact insertion position of an adjacent earlier root

The augmented sorted predecessor list inserts the extra root at its actual
count of smaller predecessors. Removing that slot recovers the original list
in exactly its old order. This is an explicit indexing identity, not a garden
coloring or noncancellation assertion.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

theorem priorInsertionPosition_le_length {n : ℕ} (G : SimpleGraph (Fin n)) (j i : Fin n) :
    ((priorNonneighbors G j).filter (fun w => decide (w < i))).length ≤
      (priorNonneighbors G j).length :=
  List.length_filter_le _ _

/-- The actual zero-based insertion slot, including insertion after all old children. -/
noncomputable def priorInsertionPosition {n : ℕ} (G : SimpleGraph (Fin n)) (j i : Fin n) :
    Fin ((priorNonneighbors G j).length + 1) :=
  ⟨((priorNonneighbors G j).filter (fun w => decide (w < i))).length,
    Nat.lt_succ_of_le (priorInsertionPosition_le_length G j i)⟩

@[simp] theorem priorInsertionPosition_val {n : ℕ} (G : SimpleGraph (Fin n)) (j i : Fin n) :
    (priorInsertionPosition G j i).val =
      ((priorNonneighbors G j).filter (fun w => decide (w < i))).length := rfl

/-- Cast only the proven length equality; no vertex labels are changed. -/
noncomputable def augmentedPriorIndex {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) (hij : G.Adj i j) :
    Fin ((priorNonneighbors G j).length + 1) ≃
      Fin (augmentedPriorNonneighbors G j i).length :=
  finCongr (augmentedPriorNonneighbors_length G i j hij).symm

@[simp] theorem augmentedPriorIndex_val {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) (s : Fin ((priorNonneighbors G j).length + 1)) :
    (augmentedPriorIndex G i j hij s).val = s.val := rfl

theorem augmented_filter_lt_inserted_eq {n : ℕ} (G : SimpleGraph (Fin n)) (j i : Fin n) :
    ((augmentedPriorNonneighbors G j i).filter (fun w => decide (w < i))).length =
      ((priorNonneighbors G j).filter (fun w => decide (w < i))).length := by
  classical
  rw [← List.toFinset_card_of_nodup ((augmentedPriorNonneighbors_sortedLT G j i).nodup.filter _),
    ← List.toFinset_card_of_nodup ((priorNonneighbors_sortedLT G j).nodup.filter _)]
  congr 1
  ext w
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hw, hwi⟩
    rcases (mem_augmentedPriorNonneighbors G j i w).mp hw with rfl | hw
    · exact False.elim (lt_irrefl _ hwi)
    · exact ⟨(mem_priorNonneighbors G w j).mpr hw, hwi⟩
  · rintro ⟨hw, hwi⟩
    exact ⟨(mem_augmentedPriorNonneighbors G j i w).mpr
      (Or.inr ((mem_priorNonneighbors G w j).mp hw)), hwi⟩

/-- The actual inserted-root entry sits at its actual insertion-count slot. -/
theorem augmentedPriorVertex_at_insertion {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) :
    augmentedPriorVertex G j i
      (augmentedPriorIndex G i j hij (priorInsertionPosition G j i)) = i := by
  classical
  have hmem : i ∈ augmentedPriorNonneighbors G j i :=
    (mem_augmentedPriorNonneighbors G j i i).mpr (Or.inl rfl)
  obtain ⟨r, hr⟩ := List.mem_iff_get.mp hmem
  have hc := sortedLT_filter_lt_length _ (augmentedPriorNonneighbors_sortedLT G j i) r
  rw [hr, augmented_filter_lt_inserted_eq] at hc
  have hrpos : r = augmentedPriorIndex G i j hij (priorInsertionPosition G j i) := by
    apply Fin.ext
    simpa only [augmentedPriorIndex_val, priorInsertionPosition_val] using hc.symm
  change (augmentedPriorNonneighbors G j i).get _ = i
  rw [← hrpos]
  exact hr

/-- Deleting the inserted slot preserves every other predecessor's exact position. -/
theorem augmentedPriorVertex_succAbove {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) (s : Fin (priorNonneighbors G j).length) :
    augmentedPriorVertex G j i
      (augmentedPriorIndex G i j hij ((priorInsertionPosition G j i).succAbove s)) =
      priorVertex G j s := by
  classical
  let p := priorInsertionPosition G j i
  let e := augmentedPriorIndex G i j hij
  let f : Fin (priorNonneighbors G j).length → Fin n :=
    fun r => augmentedPriorVertex G j i (e (p.succAbove r))
  have hcap : augmentedPriorVertex G j i (e p) = i :=
    augmentedPriorVertex_at_insertion G i j hij
  have hf : StrictMono f := by
    intro r t hrt
    apply augmentedPriorVertex_strictMono G j i
    change (p.succAbove r).val < (p.succAbove t).val
    exact Fin.strictMono_succAbove p hrt
  have hrange : Set.range f = Set.range (priorVertex G j) := by
    ext v
    constructor
    · rintro ⟨r, rfl⟩
      have hmem := (mem_augmentedPriorNonneighbors G j i (f r)).mp
        (List.get_mem (augmentedPriorNonneighbors G j i) (e (p.succAbove r)))
      rcases hmem with heq | hmem
      · have hei : e (p.succAbove r) = e p :=
          (augmentedPriorVertex_strictMono G j i).injective (heq.trans hcap.symm)
        exact False.elim (p.succAbove_ne r (e.injective hei))
      · obtain ⟨q, hq⟩ := List.mem_iff_get.mp ((mem_priorNonneighbors G (f r) j).mpr hmem)
        exact ⟨q, hq⟩
    · rintro ⟨r, rfl⟩
      have hmem : priorVertex G j r ∈ augmentedPriorNonneighbors G j i :=
        (mem_augmentedPriorNonneighbors G j i _).mpr
          (Or.inr ((mem_priorNonneighbors G _ j).mp (List.get_mem _ r)))
      obtain ⟨q, hq⟩ := List.mem_iff_get.mp hmem
      let q₀ := e.symm q
      have hq₀ : q₀ ≠ p := by
        intro heq
        have he : e p = q := by rw [← heq]; exact e.apply_symm_apply q
        have hvi : priorVertex G j r = i := hq.symm.trans (he ▸ hcap)
        exact adjacent_not_mem_priorNonneighbors G i j hij (hvi ▸ List.get_mem _ r)
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hq₀
      refine ⟨t, ?_⟩
      change augmentedPriorVertex G j i (e (p.succAbove t)) = priorVertex G j r
      rw [ht]
      change augmentedPriorVertex G j i (e (e.symm q)) = priorVertex G j r
      rw [e.apply_symm_apply]
      exact hq
  have hfun : f = priorVertex G j := (hf.range_inj (priorVertex_strictMono G j)).mp hrange
  exact congrFun hfun s

#assert_trust kernel augmentedPriorVertex_at_insertion
#assert_trust kernel augmentedPriorVertex_succAbove
#print axioms augmentedPriorVertex_at_insertion
#print axioms augmentedPriorVertex_succAbove

end NLA.Proofs.SP11
