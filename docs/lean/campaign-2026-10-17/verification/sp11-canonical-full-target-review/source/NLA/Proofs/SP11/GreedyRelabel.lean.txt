import NLA.Proofs.SP11.GreedyOrdering
import NLA.Proofs.SP11.PolynomialLSS

/-!
# Greedy relabeling for the exact SP-11 target

A complete greedy listing is transported to the natural order on `Fin n`
by an actual permutation. Graph pattern, minimum degree, and matrix rank
are invariant under that relabeling. The final reduction keeps the missing
shared-variable noncancellation theorem as an explicit premise.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP11

/-- Greediness in the natural `Fin n` order, using all strictly earlier vertices. -/
def OrderedGreedy {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ i j : Fin n, i ≤ j →
    localNonneighbors G (Finset.Iio i) i ≤ localNonneighbors G (Finset.Iio i) j

/-- Relabeling is an exact graph isomorphism, so it preserves minimum degree. -/
theorem minimumDegree_comap {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n ≃ Fin n) :
    NLA.Statements.SP11.MinimumDegree (G.comap e) =
      NLA.Statements.SP11.MinimumDegree G := by
  classical
  exact (SimpleGraph.Iso.comap e G).minDegree_eq

/-- Simultaneously reindexing both matrix axes preserves its real rank. -/
theorem rank_relabel {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin n ≃ Fin n) :
    (A.submatrix e e).rank = A.rank := Matrix.rank_submatrix A e e

/-- Reindex an exact-pattern witness along the same vertex equivalence. -/
theorem hasPattern_comap {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n ≃ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : NLA.Statements.SP11.HasPattern G A) :
    NLA.Statements.SP11.HasPattern (G.comap e) (A.submatrix e e) := by
  refine ⟨fun i j => hA.1 (e i) (e j), ?_⟩
  intro i j hij
  exact hA.2 (e i) (e j) (e.injective.ne hij)

/-- Transport a witness in the relabeled graph back to the original vertex labels. -/
theorem hasPattern_of_comap {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n ≃ Fin n)
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : NLA.Statements.SP11.HasPattern (G.comap e) A) :
    NLA.Statements.SP11.HasPattern G (A.submatrix e.symm e.symm) := by
  refine ⟨fun i j => hA.1 (e.symm i) (e.symm j), ?_⟩
  intro i j hij
  simpa only [SimpleGraph.comap_adj, Equiv.apply_symm_apply, Matrix.submatrix_apply] using
    hA.2 (e.symm i) (e.symm j) (e.symm.injective.ne hij)

/-- Counts in a relabeled prefix are counts in its actual image, not a new ordering oracle. -/
theorem localNonneighbors_comap {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n ≃ Fin n)
    (s : Finset (Fin n)) (j : Fin n) :
    localNonneighbors (G.comap e) s j = localNonneighbors G (s.image e) (e j) := by
  classical
  have hf : (s.filter (fun w => ¬ (G.comap e).Adj j w)).image e =
      (s.image e).filter (fun w => ¬ G.Adj (e j) w) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.comap_adj]
    constructor
    · rintro ⟨w, ⟨hw, hn⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, hn⟩
    · rintro ⟨⟨w, hw, rfl⟩, hn⟩
      exact ⟨w, ⟨hw, hn⟩, rfl⟩
  exact (Finset.card_image_of_injective _ e.injective).symm.trans (congrArg Finset.card hf)

/-- The predecessor-list length is the exact natural-order earlier-nonneighbor count. -/
theorem priorNonneighbors_length_eq {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n) :
    (priorNonneighbors G j).length = localNonneighbors G (Finset.Iio j) j := by
  classical
  simp only [priorNonneighbors, Finset.length_sort, localNonneighbors]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]

/-- The insertion position of an earlier vertex in the later nonneighbor list
is the number of that later vertex's nonneighbors preceding it. This applies
both to actual nonneighbor children and to an inserted adjacent root. -/
theorem priorNonneighbors_filter_lt_length {n : ℕ} (G : SimpleGraph (Fin n))
    (i j : Fin n) (hij : i ≤ j) :
    ((priorNonneighbors G j).filter (fun w => decide (w < i))).length =
      localNonneighbors G (Finset.Iio i) j := by
  classical
  have hnd : (priorNonneighbors G j).Nodup := by simp [priorNonneighbors]
  rw [← List.toFinset_card_of_nodup (hnd.filter (fun w => decide (w < i)))]
  change _ = ((Finset.Iio i).filter (fun w => ¬ G.Adj j w)).card
  congr 1
  ext w
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
    mem_priorNonneighbors, Finset.mem_filter, Finset.mem_Iio]
  constructor
  · rintro ⟨⟨_, hn⟩, hwi⟩
    exact ⟨hwi, hn⟩
  · rintro ⟨hwi, hn⟩
    exact ⟨⟨lt_of_lt_of_le hwi hij, hn⟩, hwi⟩

/-- Hall's strict child/insertion bound in the actual natural-order input lists. -/
theorem OrderedGreedy.prior_length_lt_insertionPosition {n : ℕ}
    (G : SimpleGraph (Fin n)) (hgr : OrderedGreedy G)
    (i j : Fin n) (hij : i ≤ j) :
    (priorNonneighbors G i).length <
      ((priorNonneighbors G j).filter (fun w => decide (w < i))).length + 1 := by
  rw [priorNonneighbors_length_eq, priorNonneighbors_filter_lt_length G i j hij]
  exact Nat.lt_succ_of_le (hgr i j hij)

/-- A listing equivalence sends each natural prefix to precisely the corresponding list prefix. -/
theorem prefix_image_of_listing {n : ℕ} (l : List (Fin n)) (hlen : l.length = n)
    (e : Fin n ≃ Fin n) (he : ∀ i : Fin n, e i = l[i.val]'(by omega)) (i : Fin n) :
    (Finset.Iio i).image e = (l.take i.val).toFinset := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_Iio, List.mem_toFinset]
  constructor
  · rintro ⟨j, hj, rfl⟩
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j.val, by omega, (he j).symm⟩
  · intro hv
    obtain ⟨r, hr, hrv⟩ := List.mem_take_iff_getElem.mp hv
    have hrn : r < n := by omega
    refine ⟨⟨r, hrn⟩, ?_, ?_⟩
    · exact show r < i.val by omega
    · exact (he ⟨r, hrn⟩).trans hrv

/-- Every graph has a concrete permutation into a greedy natural order and an
ambient dimension with the original degree bound and all contraction arities valid. -/
theorem exists_orderedGreedy_comap {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    ∃ (e : Fin n ≃ Fin n) (d : ℕ),
      OrderedGreedy (G.comap e) ∧
      d + NLA.Statements.SP11.MinimumDegree (G.comap e) ≤ n ∧
      ∀ j : Fin n, (priorNonneighbors (G.comap e) j).length < d := by
  classical
  obtain ⟨l, hnd, hall, hgr⟩ := exists_greedyListing G
  have hlen : l.length = n := by simpa using greedyListing_length hnd hall
  let e0 : Fin l.length ≃ Fin n := hnd.getEquivOfForallMemList l hall
  let e : Fin n ≃ Fin n := (finCongr hlen.symm).trans e0
  have he (i : Fin n) : e i = l[i.val]'(by omega) := rfl
  have hp (i j : Fin n) :
      localNonneighbors (G.comap e) (Finset.Iio i) j =
        localNonneighbors G (l.take i.val).toFinset (l[j.val]'(by omega)) := by
    rw [localNonneighbors_comap, prefix_image_of_listing l hlen e he, he]
  obtain ⟨d, _hd, hdim, hcount⟩ := greedy_dimension_bound hn G hlen hnd hall hgr
  refine ⟨e, d, ?_, ?_, ?_⟩
  · intro i j hij
    rw [hp, hp]
    have h := hgr.count_le_later G i.val j.val (by omega) (by omega) hij
    simpa only [Finset.empty_union] using h
  · rw [minimumDegree_comap]
    exact hdim
  · intro j
    rw [priorNonneighbors_length_eq, hp]
    exact hcount j.val (by omega)

/-- A proof of Hall's precise polynomial noncancellation claim in naturally
greedy orders would prove the entire frozen target. This theorem does not
supply that noncancellation proof, and leaves it explicitly quantified. -/
theorem target_of_orderedGreedy_polynomialLSS_nonzero
    (h : ∀ (n : ℕ), 0 < n → ∀ (G : SimpleGraph (Fin n)), OrderedGreedy G →
      ∀ d : ℕ, (∀ j : Fin n, (priorNonneighbors G j).length < d) →
      ∀ i j : Fin n, i = j ∨ G.Adj i j →
        polynomialGram (polynomialLSS G d) i j ≠ 0) :
    NLA.Statements.SP11.Target := by
  intro n hn G
  obtain ⟨e, d, hgreedy, hdim, harity⟩ := exists_orderedGreedy_comap hn G
  obtain ⟨A, hA, hnullity⟩ := exists_pattern_matrix_of_polynomialLSS_nonzero (G.comap e)
    hdim (h n hn (G.comap e) hgreedy d harity)
  refine ⟨A.submatrix e.symm e.symm, hasPattern_of_comap G e A hA, ?_⟩
  rw [rank_relabel]
  rwa [minimumDegree_comap] at hnullity

#assert_trust kernel hasPattern_of_comap
#assert_trust kernel minimumDegree_comap
#assert_trust kernel priorNonneighbors_length_eq
#assert_trust kernel OrderedGreedy.prior_length_lt_insertionPosition
#assert_trust kernel exists_orderedGreedy_comap
#assert_trust kernel target_of_orderedGreedy_polynomialLSS_nonzero
#print axioms exists_orderedGreedy_comap
#print axioms target_of_orderedGreedy_polynomialLSS_nonzero

end NLA.Proofs.SP11
