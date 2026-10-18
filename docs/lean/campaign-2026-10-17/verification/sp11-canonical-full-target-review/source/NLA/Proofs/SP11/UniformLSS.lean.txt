import NLA.Proofs.SP11.AlternatingContraction
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sort

/-!
# The finite uniform LSS recursion

Each vertex contracts an alternating tensor against the vectors of its earlier
nonneighbors. This module constructs those vectors and proves exact
orthogonality of nonedges. It does not prove that edge or diagonal inner
products are nonzero; that is Hall's separate non-cancellation theorem.

Source: H. Tracy Hall, *The Delta Theorem*, arXiv:2601.01211v1, Sections 3–5.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

/-- Earlier nonneighbors in the fixed increasing vertex order. A vertex does
not occur in its own input list. -/
noncomputable def priorNonneighbors {n : ℕ} (G : SimpleGraph (Fin n))
    (j : Fin n) : List (Fin n) := by
  classical
  exact ((Finset.univ : Finset (Fin n)).filter
    (fun i => i < j ∧ ¬ G.Adj j i)).sort (· ≤ ·)

theorem mem_priorNonneighbors {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) :
    i ∈ priorNonneighbors G j ↔ i < j ∧ ¬ G.Adj j i := by
  classical
  simp [priorNonneighbors]

/-- The actual predecessor at each contraction slot. -/
noncomputable def priorVertex {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) : Fin n :=
  (priorNonneighbors G j).get s

theorem priorVertex_lt {n : ℕ} (G : SimpleGraph (Fin n)) (j : Fin n)
    (s : Fin (priorNonneighbors G j).length) : (priorVertex G j s).val < j.val := by
  exact ((mem_priorNonneighbors G _ _).mp (List.get_mem _ s)).1

variable {R : Type*} [CommRing R] {n d : ℕ}

/-- One independently chosen alternating form per vertex. This is data, not
an assumption that the final graph representation is faithful. -/
abbrev VertexForms (G : SimpleGraph (Fin n)) (R : Type*) [CommRing R] (d : ℕ) :=
  (j : Fin n) → (CoordinateVector R d) [⋀^Fin ((priorNonneighbors G j).length + 1)]→ₗ[R] R

/-- Finite well-founded recursion on vertex labels. Every recursive argument
belongs to the strictly earlier predecessor list. -/
noncomputable def uniformLSS (G : SimpleGraph (Fin n)) (a : VertexForms G R d) :
    Fin n → CoordinateVector R d :=
  (measure (fun j : Fin n => j.val)).wf.fix
    (fun j rec => alternatingContraction (a j)
      (fun s => rec (priorVertex G j s) (priorVertex_lt G j s)))

theorem uniformLSS_eq (G : SimpleGraph (Fin n)) (a : VertexForms G R d) (j : Fin n) :
    uniformLSS G a j = alternatingContraction (a j)
      (fun s => uniformLSS G a (priorVertex G j s)) := by
  unfold uniformLSS
  rw [WellFounded.fix_eq]

/-- The recursive construction is orthogonal to each of its input vectors. -/
theorem uniformLSS_orthogonal_prior (G : SimpleGraph (Fin n))
    (a : VertexForms G R d) (j : Fin n) (s : Fin (priorNonneighbors G j).length) :
    uniformLSS G a j ⬝ᵥ uniformLSS G a (priorVertex G j s) = 0 := by
  conv_lhs => rw [uniformLSS_eq G a j]
  exact alternatingContraction_orthogonal _ _ s

/-- Every distinct nonedge has exactly zero inner product. There is no
probability qualifier, dimension bound, genericity hypothesis or tolerance. -/
theorem uniformLSS_orthogonal_nonedge (G : SimpleGraph (Fin n))
    (a : VertexForms G R d) (i j : Fin n) (hij : i ≠ j) (hnot : ¬ G.Adj i j) :
    uniformLSS G a i ⬝ᵥ uniformLSS G a j = 0 := by
  wlog hlt : j < i generalizing i j
  · rw [dotProduct_comm]
    apply this j i hij.symm (fun h => hnot h.symm)
    exact lt_of_le_of_ne (le_of_not_gt hlt) hij
  have hmem : j ∈ priorNonneighbors G i :=
    (mem_priorNonneighbors G j i).mpr ⟨hlt, hnot⟩
  obtain ⟨s, hs⟩ := List.mem_iff_get.mp hmem
  have hv : priorVertex G i s = j := hs
  rw [← hv]
  exact uniformLSS_orthogonal_prior G a i s

#assert_trust kernel uniformLSS_eq
#assert_trust kernel uniformLSS_orthogonal_prior
#assert_trust kernel uniformLSS_orthogonal_nonedge
#print axioms uniformLSS_orthogonal_nonedge

end NLA.Proofs.SP11
