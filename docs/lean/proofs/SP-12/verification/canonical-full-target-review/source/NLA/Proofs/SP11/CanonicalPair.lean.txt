import NLA.Proofs.SP11.CanonicalColoring
import NLA.Proofs.SP11.DoubleHistogramWeights

/-!
# An actual admissible canonical paired coloring

The later top root inserts the common cap among its children. The earlier
root and all subtrees have normal child colors. Greediness proves every
node tensor sees distinct colors; this establishes a nonzero summand, not
that other summands cannot cancel it.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11.GardenTree

variable {V : Type*} {arity : V → ℕ} {d : ℕ}

/-- Extract the choices strictly below the output cap. -/
def belowColors : (t : GardenTree V arity) → Coloring d t → BelowColoring d t
  | .node _ _, c => c.2

@[simp] theorem withRootColor_belowColors (t : GardenTree V arity) (c : Coloring d t) :
    withRootColor t (rootColor c) (belowColors t c) = c := by cases t; rfl

/-- Join two complete colorings with an exactly shared root conduit. -/
def pairColorings (t u : GardenTree V arity) (a : Coloring d t) (b : Coloring d u)
    (_h : rootColor a = rootColor b) : DoubleColoring d t u :=
  (rootColor a, belowColors t a, belowColors u b)

@[simp] theorem leftColoring_pairColorings (t u : GardenTree V arity)
    (a : Coloring d t) (b : Coloring d u) (h : rootColor a = rootColor b) :
    leftColoring (pairColorings t u a b h) = a := withRootColor_belowColors t a

@[simp] theorem rightColoring_pairColorings (t u : GardenTree V arity)
    (a : Coloring d t) (b : Coloring d u) (h : rootColor a = rootColor b) :
    rightColoring (pairColorings t u a b h) = b := by
  change withRootColor u (rootColor a) (belowColors u b) = b
  rw [h, withRootColor_belowColors]

@[simp] theorem rootColor_insertedColoring (t : GardenTree V arity)
    (h : ArityBound d t) (p : Fin (rootArity t + 1)) :
    rootColor (insertedColoring t h p) = Fin.castLE (Nat.succ_le_of_lt (rootArity_lt t h)) p := by
  cases t
  rfl

/-- Recursive admissibility means injectivity at every actual node occurrence. -/
theorem Admissible.occurrence_injective {t : GardenTree V arity} {c : Coloring d t}
    (h : Admissible t c) (o : Occurrence t) : Function.Injective (occurrenceColors t c o) := by
  induction t with
  | node v children ih =>
    cases o with
    | inl _ => exact h.1
    | inr o =>
      rcases o with ⟨s, o⟩
      exact ih s (h.2 s) o

/-- Every admissible coloring has a nonzero actual product of signs. -/
theorem coloringSign_ne_zero {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    {t : GardenTree V arity} {c : Coloring d t} (h : Admissible t c) :
    coloringSign R t c ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro o _
  exact colorSign_ne_zero _ (h.occurrence_injective o)

/-- Nonzero coefficients are retained when the two admissible trees share a cap. -/
theorem doubleColoringSign_ne_zero {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    {t u : GardenTree V arity} {c : DoubleColoring d t u}
    (hl : Admissible t (leftColoring c)) (hr : Admissible u (rightColoring c)) :
    doubleColoringSign R t u c ≠ 0 := by
  classical
  change (∏ o : Occurrence t ⊕ Occurrence u, _) ≠ 0
  rw [Fintype.prod_sum_type]
  exact mul_ne_zero (coloringSign_ne_zero hl) (coloringSign_ne_zero hr)

end NLA.Proofs.SP11.GardenTree

namespace NLA.Proofs.SP11

/-- Zero-based cap insertion position among the later root's actual children. -/
noncomputable def canonicalCapPosition {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) : ℕ :=
  ((priorNonneighbors G j).filter (fun w => decide (w < i))).length

theorem canonicalCapPosition_le {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    canonicalCapPosition G i j ≤ (priorNonneighbors G j).length := by
  exact List.length_filter_le _ _

noncomputable def canonicalInsertionSlot {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) : Fin ((lssGarden G j).rootArity + 1) :=
  ⟨canonicalCapPosition G i j, by
    rw [lssGarden_rootArity]
    exact Nat.lt_succ_of_le (canonicalCapPosition_le G i j)⟩

noncomputable def canonicalLateColoring {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    GardenTree.Coloring.{0, 0} d (lssGarden G j) :=
  GardenTree.insertedColoring (lssGarden G j) (lssGarden_arityBound G hd j)
    (canonicalInsertionSlot G i j)

theorem canonicalLate_root_val {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    (GardenTree.rootColor (canonicalLateColoring G hd i j)).val = canonicalCapPosition G i j := by
  rw [canonicalLateColoring, GardenTree.rootColor_insertedColoring]
  rfl

noncomputable def canonicalEarlyColoring {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    GardenTree.Coloring.{0, 0} d (lssGarden G i) :=
  GardenTree.normalColoring (lssGarden G i) (lssGarden_arityBound G hd i)
    (GardenTree.rootColor (canonicalLateColoring G hd i j))

/-- The actual finite canonical paired summand, in the original shared-variable expansion. -/
noncomputable def canonicalPair {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    GardenTree.DoubleColoring d (lssGarden G i) (lssGarden G j) :=
  GardenTree.pairColorings _ _ (canonicalEarlyColoring G hd i j)
    (canonicalLateColoring G hd i j) (GardenTree.rootColor_normalColoring _ _ _)

@[simp] theorem canonicalPair_left {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    GardenTree.leftColoring (canonicalPair G hd i j) = canonicalEarlyColoring G hd i j := by
  change GardenTree.withRootColor _ (GardenTree.rootColor (canonicalEarlyColoring G hd i j))
    (GardenTree.belowColors _ (canonicalEarlyColoring G hd i j)) = _
  exact GardenTree.withRootColor_belowColors _ _

@[simp] theorem canonicalPair_right {n d : ℕ} (G : SimpleGraph (Fin n))
    (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d) (i j : Fin n) :
    GardenTree.rightColoring (canonicalPair G hd i j) = canonicalLateColoring G hd i j := by
  change GardenTree.withRootColor _ (GardenTree.rootColor (canonicalEarlyColoring G hd i j))
    (GardenTree.belowColors _ (canonicalLateColoring G hd i j)) = _
  have hcap : GardenTree.rootColor (canonicalEarlyColoring G hd i j) =
      GardenTree.rootColor (canonicalLateColoring G hd i j) :=
    GardenTree.rootColor_normalColoring _ _ _
  rw [hcap]
  exact GardenTree.withRootColor_belowColors _ _

/-- The canonical pair is admissible for any ordered root pair. Nonedge pairs
can still have cancellation, so this theorem asserts no Gram nonvanishing. -/
theorem canonicalPair_admissible {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i j : Fin n) (hij : i ≤ j) :
    GardenTree.Admissible (lssGarden G i) (GardenTree.leftColoring (canonicalPair G hd i j)) ∧
      GardenTree.Admissible (lssGarden G j) (GardenTree.rightColoring (canonicalPair G hd i j)) := by
  have hcap : GardenTree.rootColor (canonicalEarlyColoring G hd i j) =
      GardenTree.rootColor (canonicalLateColoring G hd i j) :=
    GardenTree.rootColor_normalColoring _ _ _
  constructor
  · change GardenTree.Admissible (lssGarden G i)
      (GardenTree.withRootColor _ (GardenTree.rootColor (canonicalEarlyColoring G hd i j))
        (GardenTree.belowColors _ (canonicalEarlyColoring G hd i j)))
    rw [GardenTree.withRootColor_belowColors]
    apply GardenTree.normalColoring_admissible _ _ (lssGarden_normalStructure G hgr i)
    rw [lssGarden_rootArity, canonicalLate_root_val]
    have hb := hgr.prior_length_lt_insertionPosition G i j hij
    exact Nat.le_of_lt_succ hb
  · change GardenTree.Admissible (lssGarden G j)
      (GardenTree.withRootColor _ (GardenTree.rootColor (canonicalEarlyColoring G hd i j))
        (GardenTree.belowColors _ (canonicalLateColoring G hd i j)))
    rw [hcap, GardenTree.withRootColor_belowColors]
    exact GardenTree.insertedColoring_admissible _ _ (lssGarden_normalStructure G hgr j) _

/-- A canonical summand really contributes a nonzero signed monomial. The
remaining uniqueness theorem must still rule out cancellation by other summands. -/
theorem canonicalPair_sign_ne_zero {n d : ℕ} (G : SimpleGraph (Fin n))
    (hgr : OrderedGreedy G) (hd : ∀ j : Fin n, (priorNonneighbors G j).length < d)
    (i j : Fin n) (hij : i ≤ j) :
    GardenTree.doubleColoringSign ℝ (lssGarden G i) (lssGarden G j) (canonicalPair G hd i j) ≠ 0 := by
  obtain ⟨hl, hr⟩ := canonicalPair_admissible G hgr hd i j hij
  exact GardenTree.doubleColoringSign_ne_zero hl hr

#assert_trust kernel canonicalPair_admissible
#assert_trust kernel canonicalPair_sign_ne_zero
#print axioms canonicalPair_sign_ne_zero

end NLA.Proofs.SP11
