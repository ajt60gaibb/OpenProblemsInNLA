import NLA.Proofs.SP12.Chromatic
import NLA.Statements.SP11

/-! Actual vertex deletions and the critical-subgraph degree argument.
Deletion is an injective copy of all vertices except the selected one. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP12

open NLA.Statements.SP12

/-- A fixed finite permutation, independent of ambient decidability instances. -/
def swapZero {h : ℕ} (v : Fin (h + 1)) : Fin (h + 1) ≃ Fin (h + 1) :=
  Equiv.swap 0 v

@[simp] theorem swapZero_zero {h : ℕ} (v : Fin (h + 1)) : swapZero v 0 = v :=
  Equiv.swap_apply_left 0 v

@[simp] theorem swapZero_involutive {h : ℕ} (v w : Fin (h + 1)) :
    swapZero v (swapZero v w) = w := Equiv.swap_apply_self 0 v w

/-- Relabel the deleted vertex to zero, then retain all successors. -/
noncomputable def deletionEmbedding {h : ℕ} (v : Fin (h + 1)) : Fin h ↪ Fin (h + 1) :=
  ⟨fun i => swapZero v i.succ, (swapZero v).injective.comp (Fin.succ_injective h)⟩

noncomputable def deleteVertex {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (v : Fin (h + 1)) : SimpleGraph (Fin h) :=
  (G.comap (swapZero v)).comap Fin.succ

theorem deleteVertex_eq_comap {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (v : Fin (h + 1)) : deleteVertex G v = G.comap (deletionEmbedding v) := rfl

theorem deletionEmbedding_ne {h : ℕ} (v : Fin (h + 1)) (i : Fin h) :
    deletionEmbedding v i ≠ v := by
  change swapZero v i.succ ≠ v
  intro hh
  have he := (swapZero v).injective (hh.trans (swapZero_zero v).symm)
  exact i.succ_ne_zero he

/-- This copy retains every original vertex except v. -/
theorem deletionEmbedding_range {h : ℕ} (v : Fin (h + 1)) :
    Set.range (deletionEmbedding v) = {w | w ≠ v} := by
  ext w
  constructor
  · rintro ⟨i, rfl⟩
    exact deletionEmbedding_ne v i
  · intro hw
    have he : swapZero v w ≠ 0 := by
      intro he
      have hh := congrArg (swapZero v) he
      apply hw
      simpa only [swapZero_involutive, swapZero_zero] using hh
    refine ⟨(swapZero v w).pred he, ?_⟩
    change swapZero v ((swapZero v w).pred he).succ = w
    rw [Fin.succ_pred]
    exact swapZero_involutive v w

theorem chromatic_delete_le {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (v : Fin (h + 1)) : ChromaticNumber (deleteVertex G v) ≤ ChromaticNumber G := by
  rw [deleteVertex_eq_comap]
  exact chromatic_comap_le G _

theorem degree_zero_swap {h : ℕ} (G : SimpleGraph (Fin (h + 1))) (v : Fin (h + 1)) :
    (by classical exact (G.comap (swapZero v)).degree 0) =
      (by classical exact G.degree v) := by
  classical
  have hh := (SimpleGraph.Iso.comap (swapZero v) G).degree_eq 0
  change G.degree (swapZero v 0) = (G.comap (swapZero v)).degree 0 at hh
  simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh ⊢
  simpa only [swapZero_zero] using hh.symm

theorem chromatic_delete_eq_of_degree_lt {h : ℕ}
    (G : SimpleGraph (Fin (h + 1))) (v : Fin (h + 1))
    (hdeg : by classical exact G.degree v < ChromaticNumber G - 1) :
    ChromaticNumber (deleteVertex G v) = ChromaticNumber G := by
  classical
  have hs := chromatic_delete_zero_eq (G.comap (swapZero v)) (by
    rw [chromatic_comap_equiv]
    have hh := degree_zero_swap G v
    change (G.comap (swapZero v)).degree 0 = G.degree v at hh
    simp only [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card] at hh hdeg ⊢
    rw [hh]
    exact hdeg)
  simpa [deleteVertex, chromatic_comap_equiv] using hs

/-- Failure of the critical degree bound identifies an actual removable vertex. -/
theorem exists_chromatic_preserving_deletion {h : ℕ}
    (G : SimpleGraph (Fin (h + 1)))
    (hmin : NLA.Statements.SP11.MinimumDegree G < ChromaticNumber G - 1) :
    ∃ v : Fin (h + 1), ChromaticNumber (deleteVertex G v) = ChromaticNumber G := by
  classical
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  refine ⟨v, chromatic_delete_eq_of_degree_lt G v ?_⟩
  change G.minDegree < ChromaticNumber G - 1 at hmin
  rwa [hv] at hmin

/-- Vertex-critical means each actual single-vertex deletion lowers chi. -/
def VertexCritical {h : ℕ} (G : SimpleGraph (Fin (h + 1))) : Prop :=
  ∀ v, ChromaticNumber (deleteVertex G v) < ChromaticNumber G

/-- The exact chromatic lower degree bound for every nonempty critical graph. -/
theorem critical_minDegree {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (hcrit : VertexCritical G) :
    ChromaticNumber G - 1 ≤ NLA.Statements.SP11.MinimumDegree G := by
  by_contra! hlt
  obtain ⟨v, hv⟩ := exists_chromatic_preserving_deletion G hlt
  have hc := hcrit v
  omega

/-- An actual induced embedded subgraph has the same chi and sufficient degree.
This finite induction constructs its core rather than assuming a supplied one. -/
theorem exists_induced_degree_core : ∀ (n : ℕ), 0 < n → ∀ G : SimpleGraph (Fin n),
    ∃ (m : ℕ) (_hm : 0 < m) (e : Fin m ↪ Fin n),
      ChromaticNumber (G.comap e) = ChromaticNumber G ∧
      ChromaticNumber G - 1 ≤ NLA.Statements.SP11.MinimumDegree (G.comap e) := by
  intro n
  induction n with
  | zero => intro hn; omega
  | succ h ih =>
    intro _hn G
    by_cases hb : ChromaticNumber G - 1 ≤ NLA.Statements.SP11.MinimumDegree G
    · refine ⟨h + 1, Nat.succ_pos h, Function.Embedding.refl _, ?_, ?_⟩
      · rfl
      · exact hb
    · have hlt := lt_of_not_ge hb
      obtain ⟨v, hv⟩ := exists_chromatic_preserving_deletion G hlt
      have hh : 0 < h := by
        have hc := chromatic_le_order (deleteVertex G v)
        have hp := chromatic_pos (Nat.succ_pos h) G
        omega
      obtain ⟨m, hm, e, he, hd⟩ := ih hh (deleteVertex G v)
      refine ⟨m, hm, e.trans (deletionEmbedding v), ?_, ?_⟩
      · have hcomp : G.comap (e.trans (deletionEmbedding v)) = (deleteVertex G v).comap e := rfl
        rw [hcomp, he, hv]
      · change ChromaticNumber G - 1 ≤
          NLA.Statements.SP11.MinimumDegree ((deleteVertex G v).comap e)
        rwa [hv] at hd

#assert_trust kernel deletionEmbedding_range
#assert_trust kernel critical_minDegree
#assert_trust kernel exists_induced_degree_core
#print axioms critical_minDegree
#print axioms exists_induced_degree_core

end NLA.Proofs.SP12
