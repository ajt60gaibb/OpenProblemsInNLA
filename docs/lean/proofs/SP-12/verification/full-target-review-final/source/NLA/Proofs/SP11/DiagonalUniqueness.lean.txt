import NLA.Proofs.SP11.CanonicalOutputs
import NLA.Proofs.SP11.OrdinaryBlockers
import NLA.Proofs.SP11.DoubleOccurrenceShape

/-!
# Unique canonical summand for the diagonal Gram polynomial

Both top roots share the cap equal to their number of children. Every lower
output has its ordinary sibling index. Actual injectivity supplies all the
earlier-label blockers, including at either top root.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11.GardenTree

theorem normal_tree_blockers {n d : ℕ} {a : Fin n → ℕ}
    (t : GardenTree (Fin n) a) (f : (v : Fin n) → Fin (a v) → Fin n)
    (ht : HasChildLabels f t) (hf : ∀ v, StrictMono (f v))
    (hlt : ∀ v s, f v s < v) (best actual : Coloring d t)
    (hroot : (occurrenceColors t best (rootOccurrence t) 0).val =
      a (occurrenceLabel t (rootOccurrence t)))
    (hinputs : ∀ (o : Occurrence t) (s : Fin (a (occurrenceLabel t o))),
      (occurrenceColors t best o s.succ).val = s.val)
    (hinj : ∀ o, Function.Injective (occurrenceColors t actual o))
    (o : Occurrence t) :
    ∀ q : ℕ, q < (occurrenceColors t best o 0).val →
      ∃ p, occurrenceLabel t p < occurrenceLabel t o ∧
        (occurrenceColors t best p 0).val = q ∧
        (occurrenceColors t actual o 0).val ≠ (occurrenceColors t actual p 0).val := by
  by_cases ho : IsRootOccurrence t o
  · have heq := (isRootOccurrence_iff_eq t o).mp ho
    subst o
    intro q hq
    rw [hroot] at hq
    let s : Fin (a (occurrenceLabel t (rootOccurrence t))) := ⟨q, hq⟩
    refine ⟨childOccurrence t (rootOccurrence t) s, ?_, ?_, ?_⟩
    · rw [occurrenceLabel_childOccurrence f t ht]
      exact hlt _ s
    · rw [← occurrenceColors_childOccurrence]
      exact hinputs _ s
    · intro hcolors
      have he : occurrenceColors t actual (rootOccurrence t) 0 =
          occurrenceColors t actual (rootOccurrence t) s.succ := by
        rw [occurrenceColors_childOccurrence]
        exact Fin.ext hcolors
      exact Fin.succ_ne_zero s ((hinj _ he).symm)
  · obtain ⟨p, s, hps⟩ := exists_parent_of_not_root t o ho
    rw [← hps]
    apply child_occurrence_blockers t f ht hf best actual p
    · intro r
      rw [← occurrenceColors_childOccurrence]
      exact hinputs p r
    · exact hinj p

end GardenTree

theorem canonicalCapPosition_diagonal {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    canonicalCapPosition G i i = (priorNonneighbors G i).length := by
  classical
  unfold canonicalCapPosition
  congr 1
  apply List.filter_eq_self.mpr
  intro v hv
  exact decide_eq_true ((mem_priorNonneighbors G v i).mp hv).1

theorem canonicalInsertionSlot_diagonal {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    canonicalInsertionSlot G i i = Fin.last (lssGarden G i).rootArity := by
  apply Fin.ext
  change canonicalCapPosition G i i = (lssGarden G i).rootArity
  rw [canonicalCapPosition_diagonal, lssGarden_rootArity]

theorem canonicalLate_diagonal_input_val {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i : Fin n)
    (o : GardenTree.Occurrence (lssGarden G i))
    (s : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i) o)).length) :
    (GardenTree.occurrenceColors (lssGarden G i) (canonicalLateColoring G hd i i) o s.succ).val =
      s.val := by
  by_cases ho : GardenTree.IsRootOccurrence (lssGarden G i) o
  · have heq := (GardenTree.isRootOccurrence_iff_eq _ o).mp ho
    subst o
    let r : Fin (lssGarden G i).rootArity :=
      Fin.cast (GardenTree.rootOccurrence_arity_eq (lssGarden G i)) s
    have h := GardenTree.insertedColoring_root_input_val (lssGarden G i)
      (lssGarden_arityBound G hd i) (canonicalInsertionSlot G i i) r
    rw [canonicalInsertionSlot_diagonal, Fin.succAbove_last_apply] at h
    simpa [canonicalLateColoring, canonicalInsertionSlot_diagonal, r] using h
  · exact GardenTree.insertedColoring_input_val_of_not_root (lssGarden G i)
      (lssGarden_arityBound G hd i) (canonicalInsertionSlot G i i) o ho s

theorem canonicalPair_diagonal_unique {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i : Fin n)
    (actual : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G i))
    (ha : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G i) actual ≠ 0)
    (he : GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G i) actual =
      GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G i) (canonicalPair G hd i i)) :
    actual = canonicalPair G hd i i := by
  apply doubleLSS_coloring_eq_of_exponent_eq_and_blockers G i i actual (canonicalPair G hd i i)
    ha (canonicalPair_sign_ne_zero G hgr hd i i le_rfl) he
  intro o
  right
  cases o with
  | inl o =>
    have hroot : (GardenTree.occurrenceColors (lssGarden G i)
        (GardenTree.leftColoring (canonicalPair G hd i i))
        (GardenTree.rootOccurrence (lssGarden G i)) 0).val =
        (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i)
          (GardenTree.rootOccurrence (lssGarden G i)))).length := by
      rw [canonicalPair_left, GardenTree.occurrenceColors_rootOccurrence,
        canonicalEarlyColoring, GardenTree.rootColor_normalColoring,
        canonicalLate_root_val, canonicalCapPosition_diagonal,
        GardenTree.occurrenceLabel_rootOccurrence, lssGarden_rootLabel]
    have hinputs (p : GardenTree.Occurrence (lssGarden G i))
        (s : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i) p)).length) :
        (GardenTree.occurrenceColors (lssGarden G i)
          (GardenTree.leftColoring (canonicalPair G hd i i)) p s.succ).val = s.val := by
      rw [canonicalPair_left]
      exact GardenTree.normalColoring_input_val _ _ _ p s
    have hb := GardenTree.normal_tree_blockers (lssGarden G i) (priorVertex G)
      (lssGarden_hasChildLabels G i) (priorVertex_strictMono G)
      (priorVertex_label_lt_parent G) (GardenTree.leftColoring (canonicalPair G hd i i))
      (GardenTree.leftColoring actual) hroot hinputs
      (fun p => GardenTree.doubleOccurrenceColors_injective_of_sign_ne_zero _ _ actual ha (.inl p)) o
    intro q hq
    obtain ⟨p, hp, hbest, hne⟩ := hb q hq
    exact ⟨.inl p, hp, hbest, hne⟩
  | inr o =>
    have hroot : (GardenTree.occurrenceColors (lssGarden G i)
        (GardenTree.rightColoring (canonicalPair G hd i i))
        (GardenTree.rootOccurrence (lssGarden G i)) 0).val =
        (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i)
          (GardenTree.rootOccurrence (lssGarden G i)))).length := by
      rw [canonicalPair_right, GardenTree.occurrenceColors_rootOccurrence,
        canonicalLate_root_val, canonicalCapPosition_diagonal,
        GardenTree.occurrenceLabel_rootOccurrence, lssGarden_rootLabel]
    have hinputs (p : GardenTree.Occurrence (lssGarden G i))
        (s : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i) p)).length) :
        (GardenTree.occurrenceColors (lssGarden G i)
          (GardenTree.rightColoring (canonicalPair G hd i i)) p s.succ).val = s.val := by
      rw [canonicalPair_right]
      exact canonicalLate_diagonal_input_val G hd i p s
    have hb := GardenTree.normal_tree_blockers (lssGarden G i) (priorVertex G)
      (lssGarden_hasChildLabels G i) (priorVertex_strictMono G)
      (priorVertex_label_lt_parent G) (GardenTree.rightColoring (canonicalPair G hd i i))
      (GardenTree.rightColoring actual) hroot hinputs
      (fun p => GardenTree.doubleOccurrenceColors_injective_of_sign_ne_zero _ _ actual ha (.inr p)) o
    intro q hq
    obtain ⟨p, hp, hbest, hne⟩ := hb q hq
    exact ⟨.inr p, hp, hbest, hne⟩

#assert_trust kernel GardenTree.normal_tree_blockers
#assert_trust kernel canonicalLate_diagonal_input_val
#assert_trust kernel canonicalPair_diagonal_unique
#print axioms canonicalPair_diagonal_unique

end NLA.Proofs.SP11
