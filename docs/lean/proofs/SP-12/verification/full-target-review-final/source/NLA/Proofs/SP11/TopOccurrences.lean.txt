import NLA.Proofs.SP11.CanonicalOutputs
import NLA.Proofs.SP11.PriorInsertion
import NLA.Proofs.SP11.AugmentedColors
import NLA.Proofs.SP11.OrdinaryBlockers
import NLA.Proofs.SP11.DoubleOccurrenceShape

/-!
# The augmented occurrence list at the two top roots

The inserted entry is the earlier root itself; all other entries are actual
children of the later root. Labels follow the true augmented predecessor list,
and all output colors are a reindexing of the one later-root tensor.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

@[simp] theorem lssRootOccurrence_label {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    GardenTree.occurrenceLabel (lssGarden G j) (GardenTree.rootOccurrence (lssGarden G j)) = j := by
  rw [GardenTree.occurrenceLabel_rootOccurrence, lssGarden_rootLabel]

/-- Cast only the equality between the actual root label and its original label. -/
noncomputable def rootChildSlot {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) :
    Fin (priorNonneighbors G (GardenTree.occurrenceLabel (lssGarden G j)
      (GardenTree.rootOccurrence (lssGarden G j)))).length :=
  Fin.cast (congrArg (fun v => (priorNonneighbors G v).length)
    (lssRootOccurrence_label G j)).symm s

noncomputable def rootChildOccurrence {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) : GardenTree.Occurrence (lssGarden G j) :=
  GardenTree.childOccurrence (lssGarden G j) (GardenTree.rootOccurrence (lssGarden G j))
    (rootChildSlot G j s)

theorem priorVertex_cast_label {n : ℕ} (G : SimpleGraph (Fin n))
    {a b : Fin n} (h : a = b) (s : Fin (priorNonneighbors G b).length) :
    priorVertex G a (Fin.cast (congrArg (fun v => (priorNonneighbors G v).length) h).symm s) =
      priorVertex G b s := by
  subst b
  rfl

@[simp] theorem rootChildOccurrence_label {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) :
    GardenTree.occurrenceLabel (lssGarden G j) (rootChildOccurrence G j s) = priorVertex G j s := by
  rw [rootChildOccurrence, lssGarden_childOccurrence_label]
  exact priorVertex_cast_label G (lssRootOccurrence_label G j) s

theorem rootChildOccurrence_output {n d : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (c : GardenTree.Coloring.{0,0} d (lssGarden G j))
    (s : Fin (priorNonneighbors G j).length) :
    GardenTree.occurrenceColors (lssGarden G j) c (rootChildOccurrence G j s) 0 =
      GardenTree.occurrenceColors (lssGarden G j) c
        (GardenTree.rootOccurrence (lssGarden G j)) (rootChildSlot G j s).succ :=
  (GardenTree.occurrenceColors_childOccurrence _ _ _ _).symm

/-- The cap-first output tuple at an actual root inherits tensor injectivity. -/
theorem rootOutputTuple_injective {n d : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (c : GardenTree.Coloring.{0,0} d (lssGarden G j))
    (hc : Function.Injective (GardenTree.occurrenceColors (lssGarden G j) c
      (GardenTree.rootOccurrence (lssGarden G j)))) :
    Function.Injective (Fin.cons (GardenTree.rootColor c)
      (fun s => GardenTree.occurrenceColors (lssGarden G j) c (rootChildOccurrence G j s) 0)) := by
  apply Fin.cons_injective_of_injective
  · rintro ⟨s, hs⟩
    change GardenTree.occurrenceColors (lssGarden G j) c (rootChildOccurrence G j s) 0 =
      GardenTree.rootColor c at hs
    rw [rootChildOccurrence_output] at hs
    have hz := (GardenTree.occurrenceColors_rootOccurrence (lssGarden G j) c).symm
    have he : (rootChildSlot G j s).succ = 0 := hc (hs.trans hz)
    exact (rootChildSlot G j s).succ_ne_zero he
  · intro r s hrs
    change GardenTree.occurrenceColors (lssGarden G j) c (rootChildOccurrence G j r) 0 =
      GardenTree.occurrenceColors (lssGarden G j) c (rootChildOccurrence G j s) 0 at hrs
    rw [rootChildOccurrence_output, rootChildOccurrence_output] at hrs
    have he := hc hrs
    have hv : r.val = s.val := by
      have hh := congrArg Fin.val he
      simpa [rootChildSlot] using hh
    exact Fin.ext hv

/-- Actual top occurrences, indexed in the sorted augmented predecessor order. -/
noncomputable def augmentedTopOccurrence {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    Fin ((priorNonneighbors G j).length + 1) →
      GardenTree.DoubleOccurrence (lssGarden G i) (lssGarden G j) :=
  augmentedColors (priorInsertionPosition G j i)
    (.inl (GardenTree.rootOccurrence (lssGarden G i)))
    (fun s => .inr (rootChildOccurrence G j s))

@[simp] theorem augmentedTopOccurrence_cap {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    augmentedTopOccurrence G i j (priorInsertionPosition G j i) =
      .inl (GardenTree.rootOccurrence (lssGarden G i)) := by
  exact augmentedColors_at_cap _ _ _

@[simp] theorem augmentedTopOccurrence_child {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (s : Fin (priorNonneighbors G j).length) :
    augmentedTopOccurrence G i j ((priorInsertionPosition G j i).succAbove s) =
      .inr (rootChildOccurrence G j s) := by
  exact augmentedColors_at_child _ _ _ _

/-- Adjacency excludes the duplicated earlier-root label and identifies the
literal ordered augmented vertex list at every top occurrence. -/
theorem augmentedTopOccurrence_label {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (hij : G.Adj i j) (s : Fin ((priorNonneighbors G j).length + 1)) :
    GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
      (augmentedTopOccurrence G i j s) =
        augmentedPriorVertex G j i (augmentedPriorIndex G i j hij s) := by
  cases s using Fin.succAboveCases (priorInsertionPosition G j i) with
  | x =>
    rw [augmentedTopOccurrence_cap]
    exact (lssRootOccurrence_label G i).trans (augmentedPriorVertex_at_insertion G i j hij).symm
  | p s =>
    rw [augmentedTopOccurrence_child]
    exact (rootChildOccurrence_label G j s).trans (augmentedPriorVertex_succAbove G i j hij s).symm

theorem augmentedTopOccurrence_label_strictMono {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : G.Adj i j) :
    StrictMono (fun s => GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
      (augmentedTopOccurrence G i j s)) := by
  intro r s hrs
  change GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
      (augmentedTopOccurrence G i j r) <
    GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
      (augmentedTopOccurrence G i j s)
  rw [augmentedTopOccurrence_label G i j hij, augmentedTopOccurrence_label G i j hij]
  apply augmentedPriorVertex_strictMono G j i
  exact hrs

/-- The actual top output colors are the single later-root tensor, reindexed
at its cap position. -/
theorem augmentedTopOccurrence_colors {n d : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n)
    (c : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j)) :
    (fun s => GardenTree.doubleOccurrenceColors (lssGarden G i) (lssGarden G j) c
      (augmentedTopOccurrence G i j s) 0) =
      augmentedColors (priorInsertionPosition G j i)
        (GardenTree.rootColor (GardenTree.rightColoring c))
        (fun s => GardenTree.occurrenceColors (lssGarden G j) (GardenTree.rightColoring c)
          (rootChildOccurrence G j s) 0) := by
  funext s
  cases s using Fin.succAboveCases (priorInsertionPosition G j i) with
  | x =>
    rw [augmentedTopOccurrence_cap, augmentedColors_at_cap]
    change GardenTree.occurrenceColors _ (GardenTree.leftColoring c)
      (GardenTree.rootOccurrence _) 0 = _
    rw [GardenTree.occurrenceColors_rootOccurrence]
    simp only [GardenTree.leftColoring, GardenTree.rightColoring, GardenTree.rootColor_withRootColor]
  | p s =>
    rw [augmentedTopOccurrence_child, augmentedColors_at_child]
    rfl

/-- A nonzero actual coefficient supplies injective colors on the entire
augmented top sibling list, including the shared cap occurrence. -/
theorem augmentedTopOccurrence_colors_injective {n d : ℕ}
    (G : SimpleGraph (Fin n)) (i j : Fin n)
    (c : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (hc : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) c ≠ 0) :
    Function.Injective (fun s => GardenTree.doubleOccurrenceColors (lssGarden G i) (lssGarden G j) c
      (augmentedTopOccurrence G i j s) 0) := by
  rw [augmentedTopOccurrence_colors]
  apply augmentedColors_injective
  apply rootOutputTuple_injective G j
  exact GardenTree.doubleOccurrenceColors_injective_of_sign_ne_zero _ _ c hc
    (.inr (GardenTree.rootOccurrence (lssGarden G j)))


/-- The canonical later-root children skip exactly the true insertion position. -/
theorem canonicalLate_rootChild_val {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n)
    (s : Fin (priorNonneighbors G j).length) :
    (GardenTree.occurrenceColors (lssGarden G j) (canonicalLateColoring G hd i j)
      (rootChildOccurrence G j s) 0).val = ((priorInsertionPosition G j i).succAbove s).val := by
  rw [rootChildOccurrence_output]
  let r : Fin (lssGarden G j).rootArity := Fin.cast (lssGarden_rootArity G j).symm s
  have h := GardenTree.insertedColoring_root_input_val (lssGarden G j)
    (lssGarden_arityBound G hd j) (canonicalInsertionSlot G i j) r
  have hslot : Fin.cast (GardenTree.rootOccurrence_arity_eq (lssGarden G j)).symm r =
      rootChildSlot G j s := by
    apply Fin.ext
    rfl
  rw [hslot] at h
  apply h.trans
  dsimp only [r, canonicalInsertionSlot, priorInsertionPosition, canonicalCapPosition]
  simp only [Fin.succAbove, Fin.lt_def, apply_ite, Fin.val_castSucc, Fin.val_succ, Fin.val_cast]
  split_ifs <;> rfl


/-- Every canonical top occurrence has exactly its augmented sibling index. -/
theorem canonicalPair_augmentedTop_val {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n)
    (s : Fin ((priorNonneighbors G j).length + 1)) :
    GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) (canonicalPair G hd i j)
      (augmentedTopOccurrence G i j s) = s.val := by
  cases s using Fin.succAboveCases (priorInsertionPosition G j i) with
  | x =>
    rw [augmentedTopOccurrence_cap]
    change (GardenTree.occurrenceColors _ (GardenTree.leftColoring (canonicalPair G hd i j))
      (GardenTree.rootOccurrence _) 0).val = _
    rw [canonicalPair_left, GardenTree.occurrenceColors_rootOccurrence,
      canonicalEarlyColoring, GardenTree.rootColor_normalColoring, canonicalLate_root_val]
    rfl
  | p s =>
    rw [augmentedTopOccurrence_child]
    change (GardenTree.occurrenceColors _ (GardenTree.rightColoring (canonicalPair G hd i j))
      (rootChildOccurrence G j s) 0).val = _
    rw [canonicalPair_right]
    exact canonicalLate_rootChild_val G hd i j s

/-- The augmented top list supplies all earlier-label blockers, including the
inserted earlier root and every child of the later root. -/
theorem augmentedTopOccurrence_blockers {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n)
    (hij : G.Adj i j)
    (actual : GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j))
    (ha : GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) actual ≠ 0)
    (s : Fin ((priorNonneighbors G j).length + 1)) :
    ∀ q : ℕ, q < GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j)
      (canonicalPair G hd i j) (augmentedTopOccurrence G i j s) →
      ∃ p, GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j) p <
          GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j)
            (augmentedTopOccurrence G i j s) ∧
        GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) (canonicalPair G hd i j) p = q ∧
        GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual
          (augmentedTopOccurrence G i j s) ≠
            GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual p := by
  apply ordered_sibling_blockers
    (GardenTree.doubleOccurrenceLabel (lssGarden G i) (lssGarden G j))
    (augmentedTopOccurrence G i j) (augmentedTopOccurrence_label_strictMono G i j hij)
    (GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) (canonicalPair G hd i j))
    (GardenTree.doubleOutputValue (lssGarden G i) (lssGarden G j) actual)
    (canonicalPair_augmentedTop_val G hd i j)
  intro r t hrt
  apply augmentedTopOccurrence_colors_injective G i j actual ha
  exact Fin.ext hrt

#assert_trust kernel augmentedTopOccurrence_label
#assert_trust kernel augmentedTopOccurrence_colors_injective
#assert_trust kernel augmentedTopOccurrence_blockers
#print axioms augmentedTopOccurrence_blockers

end NLA.Proofs.SP11
