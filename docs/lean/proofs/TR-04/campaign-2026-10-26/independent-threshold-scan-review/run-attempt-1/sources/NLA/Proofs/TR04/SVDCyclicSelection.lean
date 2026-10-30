import NLA.Proofs.TR04.SVDSelectedFrame

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR04.SVD

def tieEmbedding {p : ℕ} (h t : ℕ) (ht : h + t ≤ p) (i : Fin t) : Fin p :=
  ⟨h + i.val, lt_of_lt_of_le (Nat.add_lt_add_left i.isLt h) ht⟩

theorem tieEmbedding_injective {p h t : ℕ} (ht : h + t ≤ p) :
    Function.Injective (tieEmbedding h t ht) := by
  intro i j hij
  exact Fin.ext (Nat.add_left_cancel (congrArg (fun k : Fin p => k.val) hij))

def prefixDirections {p : ℕ} (h t : ℕ) (ht : h + t ≤ p) : Finset (Fin p) :=
  Finset.univ.image (Fin.castLE ((Nat.le_add_right h t).trans ht))

def tieDirections {p : ℕ} (h t : ℕ) (ht : h + t ≤ p) : Finset (Fin p) :=
  Finset.univ.image (tieEmbedding h t ht)

def windowDirections {p : ℕ} (h t : ℕ) [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (j : Fin t) : Finset (Fin p) :=
  (Finset.univ.filter (cyclicWindow s j)).image (tieEmbedding h t ht)

def tieSelection {p : ℕ} (h t : ℕ) [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (j : Fin t) : Finset (Fin p) :=
  prefixDirections h t ht ∪ windowDirections h t ht s j

theorem prefix_window_disjoint {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (j : Fin t) :
    Disjoint (prefixDirections h t ht) (windowDirections h t ht s j) := by
  apply Finset.disjoint_left.mpr
  intro k hk1 hk2
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hk1
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hk2
  have he := congrArg (fun i : Fin p => i.val) (ha.trans hb.symm)
  change a.val = h + b.val at he
  omega

theorem card_tieSelection {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (j : Fin t) : (tieSelection h t ht s j).card = h + s := by
  rw [tieSelection, Finset.card_union_of_disjoint (prefix_window_disjoint ht s j)]
  have hprefix : (prefixDirections h t ht).card = h := by
    have hi : Function.Injective (Fin.castLE ((Nat.le_add_right h t).trans ht)) := by
      intro i j he
      exact Fin.ext (congrArg (fun k : Fin p => k.val) he)
    rw [prefixDirections, Finset.card_image_of_injective _ hi]
    simp
  have hwindow : (windowDirections h t ht s j).card = s := by
    rw [windowDirections, Finset.card_image_of_injective _ (tieEmbedding_injective ht)]
    simpa only [Fintype.card_subtype] using card_cyclicWindow s hst j
  rw [hprefix, hwindow]

theorem sum_tieSelection {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (j : Fin t) (f : Fin p → ℝ) :
    (∑ k ∈ tieSelection h t ht s j, f k) =
      (∑ k ∈ prefixDirections h t ht, f k) +
        ∑ i : Fin t, if cyclicWindow s j i then f (tieEmbedding h t ht i) else 0 := by
  rw [tieSelection, Finset.sum_union (prefix_window_disjoint ht s j)]
  congr 1
  rw [windowDirections, Finset.sum_image
    (fun _ _ _ _ he => tieEmbedding_injective ht he), Finset.sum_filter]

theorem sum_all_tieSelections {p h t : ℕ} [NeZero t] (ht : h + t ≤ p)
    (s : ℕ) (hst : s ≤ t) (f : Fin p → ℝ) :
    (∑ j : Fin t, ∑ k ∈ tieSelection h t ht s j, f k) =
      (t : ℝ) * (∑ k ∈ prefixDirections h t ht, f k) +
        (s : ℝ) * (∑ k ∈ tieDirections h t ht, f k) := by
  simp_rw [sum_tieSelection ht s]
  rw [Finset.sum_add_distrib, sum_cyclicWindow_energy s hst,
    tieDirections, Finset.sum_image (fun _ _ _ _ he => tieEmbedding_injective ht he)]
  simp

theorem sum_indicator_finset {p : ℕ} (S : Finset (Fin p)) (f : Fin p → ℝ) :
    (∑ k : Fin p, if k ∈ S then f k else 0) = ∑ k ∈ S, f k := by
  rw [← Finset.sum_filter]
  simp

#assert_trust kernel card_tieSelection
#assert_trust kernel sum_tieSelection
#assert_trust kernel sum_all_tieSelections
#print axioms sum_all_tieSelections
end NLA.Proofs.TR04.SVD
