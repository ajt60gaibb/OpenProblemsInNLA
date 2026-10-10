import Mathlib
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

/-!
Finite simple graphs as Boolean assignments to the off-diagonal unordered
vertex pairs.  This gives the exact state-space correspondence needed to
move the parity calculation to the G(n,1/2) model.
-/

namespace MD01GraphBits

variable {n : ℕ}

abbrev Edge (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

def edgesOfBits (ξ : Edge n → Bool) : Set (Sym2 (Fin n)) :=
  {e | ∃ h : ¬ e.IsDiag, ξ ⟨e, h⟩ = true}

def graphOfBits (ξ : Edge n → Bool) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (edgesOfBits ξ)

noncomputable def bitsOfGraph (G : SimpleGraph (Fin n)) : Edge n → Bool :=
  by classical exact fun e => decide (e.val ∈ G.edgeSet)

theorem graphOfBits_edgeSet (ξ : Edge n → Bool) :
    (graphOfBits ξ).edgeSet = edgesOfBits ξ := by
  classical
  ext e
  simp only [graphOfBits, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Sym2.mem_diagSet]
  constructor
  · exact And.left
  · intro he
    exact ⟨he, he.choose⟩

theorem bitsOfGraph_graphOfBits (ξ : Edge n → Bool) :
    bitsOfGraph (graphOfBits ξ) = ξ := by
  funext e
  simp only [bitsOfGraph, graphOfBits_edgeSet, edgesOfBits]
  have h : (∃ h : ¬ e.val.IsDiag, ξ ⟨e.val, h⟩ = true) ↔ ξ e = true := by
    constructor
    · rintro ⟨h, hh⟩
      simpa [Subtype.ext_iff] using hh
    · intro hh
      exact ⟨e.property, by simpa using hh⟩
  simp [h]

theorem graphOfBits_bitsOfGraph (G : SimpleGraph (Fin n)) :
    graphOfBits (bitsOfGraph G) = G := by
  apply SimpleGraph.edgeSet_injective
  rw [graphOfBits_edgeSet]
  ext e
  simp only [edgesOfBits, Set.mem_ofPred_eq, bitsOfGraph, decide_eq_true_eq]
  constructor
  · rintro ⟨_, he⟩
    exact he
  · intro he
    exact ⟨G.not_isDiag_of_mem_edgeSet he, he⟩

noncomputable def graphBitsEquiv (n : ℕ) :
    (Edge n → Bool) ≃ SimpleGraph (Fin n) where
  toFun := graphOfBits
  invFun := bitsOfGraph
  left_inv := bitsOfGraph_graphOfBits
  right_inv := graphOfBits_bitsOfGraph

#print axioms graphOfBits_edgeSet
#print axioms bitsOfGraph_graphOfBits
#print axioms graphOfBits_bitsOfGraph

end MD01GraphBits
