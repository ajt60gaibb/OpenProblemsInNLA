import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Finset.Max
import Mathlib.Tactic
import NLA.Statements.Infrastructure
import LeanCert.Tactic.Verification

/-!
# Greedy ordering foundations for SP-11

A greedy order chooses, among the remaining vertices, a vertex with the
fewest nonneighbors in the already chosen prefix. This is equivalent to
maximizing its neighbors there. These finite combinatorial results are
independent of Hall's representation theorem.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

variable {V : Type*} [DecidableEq V]

/-- Number of vertices in `before` not adjacent to `v`. A duplicate-free
listing prefix excludes the vertex currently being chosen. -/
noncomputable def localNonneighbors (G : SimpleGraph V) (before : Finset V) (v : V) : ℕ := by
  classical
  exact (before.filter fun w ↦ ¬ G.Adj v w).card

/-- A list obeys the greedy choice at every prefix, starting from `before`. -/
def GreedyFrom (G : SimpleGraph V) (before : Finset V) (l : List V) : Prop :=
  ∀ (p : List V) (a : V) (tail : List V), l = p ++ a :: tail →
    ∀ b ∈ a :: tail,
      localNonneighbors G (before ∪ p.toFinset) a ≤
        localNonneighbors G (before ∪ p.toFinset) b

omit [DecidableEq V] in
theorem localNonneighbors_mono (G : SimpleGraph V) {s t : Finset V}
    (hst : s ⊆ t) (v : V) :
    localNonneighbors G s v ≤ localNonneighbors G t v := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ hst)

/-- Greedy completion of any finite remaining set, with no repeated vertices. -/
theorem exists_greedyFrom (G : SimpleGraph V) (remaining before : Finset V) :
    ∃ l : List V, l.Nodup ∧ l.toFinset = remaining ∧ GreedyFrom G before l := by
  classical
  induction remaining using Finset.strongInductionOn generalizing before with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨a, ha, hmin⟩ := s.exists_min_image (localNonneighbors G before) hs
      obtain ⟨l, hnodup, hset, hgreedy⟩ :=
        ih (s.erase a) (Finset.erase_ssubset ha) (insert a before)
      refine ⟨a :: l, ?_, ?_, ?_⟩
      · simp only [List.nodup_cons, hnodup, and_true]
        intro hal
        have : a ∈ s.erase a := hset ▸ List.mem_toFinset.mpr hal
        exact Finset.notMem_erase a s this
      · simp [hset, Finset.insert_erase ha]
      · intro p b tail heq c hc
        cases p with
        | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          simp only [List.toFinset_nil, Finset.union_empty]
          apply hmin c
          rcases List.mem_cons.mp hc with rfl | hc
          · exact ha
          · exact Finset.mem_of_mem_erase ((hset ▸ List.mem_toFinset.mpr hc))
        | cons v p =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, heq⟩ := heq
          have h := hgreedy p b tail heq c hc
          simpa only [List.toFinset_cons, Finset.union_insert,
            Finset.insert_union] using h
    · have : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      refine ⟨[], by simp, by simp, ?_⟩
      intro p a tail heq
      have : 0 < (p ++ a :: tail).length := by simp
      simp only [← heq, List.length_nil] at this
      omega

/-- Every finite graph admits a complete greedy listing. -/
theorem exists_greedyListing [Fintype V] (G : SimpleGraph V) :
    ∃ l : List V, l.Nodup ∧ (∀ v : V, v ∈ l) ∧ GreedyFrom G ∅ l := by
  obtain ⟨l, hnd, hset, hgr⟩ := exists_greedyFrom G Finset.univ ∅
  refine ⟨l, hnd, ?_, hgr⟩
  intro v
  exact List.mem_toFinset.mp (hset.symm ▸ Finset.mem_univ v)

/-- Earlier nonneighbors at the stage when position `i` is chosen. -/
noncomputable def precedingCount (G : SimpleGraph V) (l : List V)
    (i : ℕ) (hi : i < l.length) : ℕ :=
  localNonneighbors G (l.take i).toFinset l[i]

/-- Greediness compared to a vertex that is still unchosen at stage `i`. -/
theorem GreedyFrom.count_le_later (G : SimpleGraph V) {before : Finset V}
    {l : List V} (hgr : GreedyFrom G before l)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    localNonneighbors G (before ∪ (l.take i).toFinset) l[i] ≤
      localNonneighbors G (before ∪ (l.take i).toFinset) l[j] := by
  have hsplit : l = l.take i ++ l[i] :: l.drop (i + 1) := by
    rw [List.cons_getElem_drop_succ]
    exact (List.take_append_drop i l).symm
  have hmem : l[j] ∈ l.drop i := by
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨j - i, by omega, ?_⟩
    simp only [Nat.add_sub_of_le hij]
  rw [← List.cons_getElem_drop_succ (h := hi)] at hmem
  exact hgr (l.take i) l[i] (l.drop (i + 1)) hsplit l[j] hmem

theorem take_toFinset_mono (l : List V) {i j : ℕ} (hij : i ≤ j) :
    (l.take i).toFinset ⊆ (l.take j).toFinset := by
  intro v hv
  obtain ⟨r, hr, heq⟩ :=
    List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hv)
  apply List.mem_toFinset.mpr
  apply List.mem_take_iff_getElem.mpr
  exact ⟨r, by omega, heq⟩

/-- Hall's monotonicity observation for earlier-nonneighbor counts. -/
theorem GreedyFrom.precedingCount_mono (G : SimpleGraph V)
    {l : List V} (hgr : GreedyFrom G ∅ l)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    precedingCount G l i hi ≤ precedingCount G l j hj := by
  have h := hgr.count_le_later G i j hi hj hij
  simp only [Finset.empty_union] at h
  exact h.trans (localNonneighbors_mono G (take_toFinset_mono l hij) l[j])

/-- Number of distinct nonneighbors of `l[j]` before stage `i`.
For a duplicate-free listing and `i < j`, this is the zero-based position
of a nonneighbor child, or the insertion position of an adjacent vertex. -/
noncomputable def nonneighborPosition (G : SimpleGraph V) (l : List V)
    (i j : ℕ) (hj : j < l.length) : ℕ :=
  localNonneighbors G (l.take i).toFinset l[j]

/-- The common count inequality behind Hall's child and inserted-neighbor bounds.
It applies to every earlier vertex; adjacency is not needed. -/
theorem GreedyFrom.precedingCount_lt_position (G : SimpleGraph V)
    {l : List V} (hgr : GreedyFrom G ∅ l)
    (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    precedingCount G l i hi < nonneighborPosition G l i j hj + 1 := by
  have h := hgr.count_le_later G i j hi hj hij
  simp only [Finset.empty_union] at h
  exact Nat.lt_succ_of_le h

/-- Prefix counting is literal list counting when the listing is duplicate free. -/
theorem nonneighborPosition_eq_filter_length (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : List V} (hnd : l.Nodup) (i j : ℕ) (hj : j < l.length) :
    nonneighborPosition G l i j hj =
      ((l.take i).filter fun w ↦ decide (¬ G.Adj l[j] w)).length := by
  have hfilter := List.toFinset_card_of_nodup
    ((hnd.take : (l.take i).Nodup).filter (fun w ↦ decide (¬ G.Adj l[j] w)))
  rw [← hfilter]
  unfold nonneighborPosition localNonneighbors
  congr 1
  ext w
  simp

/-- A list with every vertex exactly once gives an actual vertex-order equivalence. -/
theorem exists_greedyEquiv [Fintype V] (G : SimpleGraph V) :
    ∃ (l : List V) (e : Fin l.length ≃ V),
      (∀ i, e i = l[i]) ∧ l.Nodup ∧ GreedyFrom G ∅ l := by
  obtain ⟨l, hnd, hall, hgr⟩ := exists_greedyListing G
  exact ⟨l, hnd.getEquivOfForallMemList l hall, by intro i; rfl, hnd, hgr⟩

/-- At the final stage of a complete listing, every vertex except the chosen
one precedes it. The count therefore has exactly the source's dimension. -/
theorem lastStageCount_eq [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {l : List V} (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l)
    (i : ℕ) (hi : i < l.length) (hlast : i + 1 = l.length) :
    precedingCount G l i hi + 1 = Fintype.card V - G.degree l[i] := by
  have hset : (l.take i).toFinset.filter (fun w ↦ ¬ G.Adj l[i] w) =
      Gᶜ.neighborFinset l[i] := by
    ext w
    simp only [Finset.mem_filter, List.mem_toFinset, SimpleGraph.mem_neighborFinset,
      SimpleGraph.compl_adj]
    constructor
    · rintro ⟨hw, hn⟩
      refine ⟨?_, hn⟩
      obtain ⟨r, hr, heq⟩ := List.mem_take_iff_getElem.mp hw
      intro he
      have hri : r = i := hnd.getElem_inj_iff.mp (heq.trans he.symm)
      omega
    · rintro ⟨hne, hn⟩
      refine ⟨?_, hn⟩
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp (hall w)
      have hri : r.val < i := by
        have hrle : r.val ≤ i := by omega
        by_contra hge
        have he : r.val = i := by omega
        have hw : l[i] = w := by simpa only [List.get_eq_getElem, he] using hr
        exact hne hw
      apply List.mem_take_iff_getElem.mpr
      exact ⟨r.val, by omega, hr⟩
  have hc : precedingCount G l i hi = Gᶜ.degree l[i] := by
    change _ = (Gᶜ.neighborFinset l[i]).card
    convert congrArg Finset.card hset using 1
    unfold precedingCount localNonneighbors
    congr 1
    ext w
    simp
  have hd := G.degree_lt_card_verts l[i]
  rw [G.degree_compl l[i]] at hc
  omega

/-- The numerical ambient-dimension consequence needed before constructing
Hall's faithful representation. It is only a combinatorial dimension bound. -/
theorem greedy_dimension_bound {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {l : List (Fin n)} (hlen : l.length = n) (hnd : l.Nodup)
    (hall : ∀ v : Fin n, v ∈ l) (hgr : GreedyFrom G ∅ l) :
    ∃ d : ℕ, d = n - G.degree l[n - 1] ∧
      d + G.minDegree ≤ n ∧
      ∀ (j : ℕ) (hj : j < l.length), precedingCount G l j hj < d := by
  have hlast : n - 1 < l.length := by omega
  have hc := lastStageCount_eq G hnd hall (n - 1) hlast (by omega)
  simp only [Fintype.card_fin] at hc
  refine ⟨n - G.degree l[n - 1], rfl, ?_, ?_⟩
  · have hmin := G.minDegree_le_degree l[n - 1]
    have hdeg := G.degree_lt_card_verts l[n - 1]
    simp only [Fintype.card_fin] at hdeg
    omega
  · intro j hj
    have hm := hgr.precedingCount_mono G j (n - 1) hj hlast (by omega)
    omega

/-- Complete listings have exactly the number of vertices of the graph. -/
theorem greedyListing_length [Fintype V] {l : List V}
    (hnd : l.Nodup) (hall : ∀ v : V, v ∈ l) : l.length = Fintype.card V := by
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (hnd.getEquivOfForallMemList l hall)

#assert_trust kernel exists_greedyFrom
#assert_trust kernel exists_greedyListing
#assert_trust kernel exists_greedyEquiv
#assert_trust kernel GreedyFrom.precedingCount_mono
#assert_trust kernel GreedyFrom.precedingCount_lt_position
#assert_trust kernel lastStageCount_eq
#assert_trust kernel greedy_dimension_bound
#print axioms exists_greedyListing
#print axioms GreedyFrom.precedingCount_mono
#print axioms lastStageCount_eq
#print axioms greedy_dimension_bound

end NLA.Proofs.SP11
