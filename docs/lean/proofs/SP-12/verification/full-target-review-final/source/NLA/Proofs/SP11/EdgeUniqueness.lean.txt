import NLA.Proofs.SP11.TopOccurrences

/-!
# Unique canonical summand for every adjacent ordered root pair

At the later root the cap is inserted in the sorted predecessor list. Its
augmented sibling list supplies all top blockers. Every lower node uses its
ordinary sibling indices; the later root itself is tied to the earlier root.
All occurrences and all variables are those of the actual shared construction.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

theorem canonicalPair_edge_unique {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i j : Fin n) (hij : i < j) (hadj : G.Adj i j)
    (actual : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (ha : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) actual ≠ 0)
    (he : GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) actual =
      GardenTree.doubleColoringExponent (lssGarden G i) (lssGarden G j) (canonicalPair G hd i j)) :
    actual = canonicalPair G hd i j := by
  apply doubleLSS_coloring_eq_of_exponent_eq_and_blockers G i j actual (canonicalPair G hd i j)
    ha (canonicalPair_sign_ne_zero G hgr hd i j hij.le) he
  intro o
  cases o with
  | inl o =>
    right
    by_cases ho : GardenTree.IsRootOccurrence (lssGarden G i) o
    · have heq := (GardenTree.isRootOccurrence_iff_eq _ o).mp ho
      subst o
      have hb := augmentedTopOccurrence_blockers G hd i j hadj actual ha
        (priorInsertionPosition G j i)
      simpa only [augmentedTopOccurrence_cap] using hb
    · obtain ⟨p, s, hps⟩ := GardenTree.exists_parent_of_not_root (lssGarden G i) o ho
      rw [← hps]
      have hbest (r : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G i) p)).length) :
          (GardenTree.occurrenceColors (lssGarden G i)
            (GardenTree.leftColoring (canonicalPair G hd i j))
            (GardenTree.childOccurrence (lssGarden G i) p r) 0).val = r.val := by
        rw [canonicalPair_left]
        exact GardenTree.normalColoring_child_output_val _ _ _ p r
      have hb := GardenTree.child_occurrence_blockers (lssGarden G i) (priorVertex G)
        (lssGarden_hasChildLabels G i) (priorVertex_strictMono G)
        (GardenTree.leftColoring (canonicalPair G hd i j)) (GardenTree.leftColoring actual) p hbest
        (GardenTree.doubleOccurrenceColors_injective_of_sign_ne_zero _ _ actual ha (.inl p)) s
      intro q hq
      obtain ⟨r, hr, hbest, hne⟩ := hb q hq
      exact ⟨.inl r, hr, hbest, hne⟩
  | inr o =>
    by_cases ho : GardenTree.IsRootOccurrence (lssGarden G j) o
    · left
      have heq := (GardenTree.isRootOccurrence_iff_eq _ o).mp ho
      subst o
      refine ⟨.inl (GardenTree.rootOccurrence (lssGarden G i)), ?_, ?_, ?_⟩
      · change GardenTree.occurrenceLabel (lssGarden G i) (GardenTree.rootOccurrence _) <
          GardenTree.occurrenceLabel (lssGarden G j) (GardenTree.rootOccurrence _)
        simpa only [lssRootOccurrence_label] using hij
      · change (GardenTree.occurrenceColors _ (GardenTree.rightColoring actual)
          (GardenTree.rootOccurrence _) 0).val =
            (GardenTree.occurrenceColors _ (GardenTree.leftColoring actual)
              (GardenTree.rootOccurrence _) 0).val
        rw [GardenTree.occurrenceColors_rootOccurrence, GardenTree.occurrenceColors_rootOccurrence]
        simp only [GardenTree.leftColoring, GardenTree.rightColoring, GardenTree.rootColor_withRootColor]
      · change (GardenTree.occurrenceColors _ (GardenTree.rightColoring (canonicalPair G hd i j))
          (GardenTree.rootOccurrence _) 0).val =
            (GardenTree.occurrenceColors _ (GardenTree.leftColoring (canonicalPair G hd i j))
              (GardenTree.rootOccurrence _) 0).val
        rw [GardenTree.occurrenceColors_rootOccurrence, GardenTree.occurrenceColors_rootOccurrence]
        simp only [GardenTree.leftColoring, GardenTree.rightColoring, GardenTree.rootColor_withRootColor]
    · right
      obtain ⟨p, s, hps⟩ := GardenTree.exists_parent_of_not_root (lssGarden G j) o ho
      rw [← hps]
      by_cases hp : GardenTree.IsRootOccurrence (lssGarden G j) p
      · have heq := (GardenTree.isRootOccurrence_iff_eq _ p).mp hp
        subst p
        let r : Fin (priorNonneighbors G j).length :=
          Fin.cast (congrArg (fun v => (priorNonneighbors G v).length) (lssRootOccurrence_label G j)) s
        have hs : rootChildSlot G j r = s := by apply Fin.ext; rfl
        have hchild : GardenTree.childOccurrence (lssGarden G j)
            (GardenTree.rootOccurrence (lssGarden G j)) s = rootChildOccurrence G j r := by
          rw [rootChildOccurrence, hs]
        rw [hchild]
        have hb := augmentedTopOccurrence_blockers G hd i j hadj actual ha
          ((priorInsertionPosition G j i).succAbove r)
        simpa only [augmentedTopOccurrence_child] using hb
      · have hbest (r : Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G j) p)).length) :
            (GardenTree.occurrenceColors (lssGarden G j)
              (GardenTree.rightColoring (canonicalPair G hd i j))
              (GardenTree.childOccurrence (lssGarden G j) p r) 0).val = r.val := by
          rw [← GardenTree.occurrenceColors_childOccurrence, canonicalPair_right]
          exact GardenTree.insertedColoring_input_val_of_not_root _ _ _ p hp r
        have hb := GardenTree.child_occurrence_blockers (lssGarden G j) (priorVertex G)
          (lssGarden_hasChildLabels G j) (priorVertex_strictMono G)
          (GardenTree.rightColoring (canonicalPair G hd i j)) (GardenTree.rightColoring actual) p hbest
          (GardenTree.doubleOccurrenceColors_injective_of_sign_ne_zero _ _ actual ha (.inr p)) s
        intro q hq
        obtain ⟨r, hr, hbest, hne⟩ := hb q hq
        exact ⟨.inr r, hr, hbest, hne⟩

#assert_trust kernel canonicalPair_edge_unique
#print axioms canonicalPair_edge_unique

end NLA.Proofs.SP11
