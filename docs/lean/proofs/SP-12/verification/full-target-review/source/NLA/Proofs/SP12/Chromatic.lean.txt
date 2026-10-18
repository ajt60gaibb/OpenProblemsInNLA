import NLA.Statements.SP12
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fin.Fin2

/-! Exact natural chromatic-number facts and low-degree vertex deletion.
All colorings use the frozen SP-12 definition; no chromatic invariant is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP12

open NLA.Statements.SP12

abbrev FinColorable {n : ℕ} (G : SimpleGraph (Fin n)) (c : ℕ) : Prop :=
  ∃ f : Fin n → Fin c, ∀ i j, G.Adj i j → f i ≠ f j

theorem colorable_order {n : ℕ} (G : SimpleGraph (Fin n)) : FinColorable G n :=
  ⟨id, fun _ _ h => h.ne⟩

theorem colorable_chromatic {n : ℕ} (G : SimpleGraph (Fin n)) :
    FinColorable G (ChromaticNumber G) :=
  Nat.sInf_mem (s := {c : ℕ | FinColorable G c}) ⟨n, colorable_order G⟩

theorem chromatic_le_of_colorable {n c : ℕ} (G : SimpleGraph (Fin n))
    (hc : FinColorable G c) : ChromaticNumber G ≤ c := Nat.sInf_le hc

theorem chromatic_le_order {n : ℕ} (G : SimpleGraph (Fin n)) :
    ChromaticNumber G ≤ n := chromatic_le_of_colorable G (colorable_order G)

theorem FinColorable.mono {n c d : ℕ} {G : SimpleGraph (Fin n)}
    (hc : FinColorable G c) (hcd : c ≤ d) : FinColorable G d := by
  obtain ⟨f, hf⟩ := hc
  refine ⟨fun i => Fin.castLE hcd (f i), fun i j hij he => hf i j hij ?_⟩
  apply Fin.ext
  exact congrArg (fun a : Fin d => a.val) he

theorem chromatic_le_iff_colorable {n c : ℕ} (G : SimpleGraph (Fin n)) :
    ChromaticNumber G ≤ c ↔ FinColorable G c :=
  ⟨fun h => (colorable_chromatic G).mono h, chromatic_le_of_colorable G⟩

theorem chromatic_empty (G : SimpleGraph (Fin 0)) : ChromaticNumber G = 0 :=
  Nat.eq_zero_of_le_zero (chromatic_le_order G)

theorem chromatic_pos {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    0 < ChromaticNumber G := by
  obtain ⟨f, _⟩ := colorable_chromatic G
  exact Nat.pos_of_ne_zero (fun h => Fin.elim0 (Fin.cast h (f ⟨0, hn⟩)))

theorem chromatic_comap_le {n m : ℕ} (G : SimpleGraph (Fin n)) (f : Fin m → Fin n) :
    ChromaticNumber (G.comap f) ≤ ChromaticNumber G := by
  obtain ⟨c, hc⟩ := colorable_chromatic G
  exact chromatic_le_of_colorable _ ⟨fun i => c (f i), fun i j hij => hc _ _ hij⟩

theorem chromatic_comap_equiv {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n ≃ Fin n) :
    ChromaticNumber (G.comap e) = ChromaticNumber G := by
  apply le_antisymm (chromatic_comap_le G e)
  obtain ⟨c, hc⟩ := colorable_chromatic (G.comap e)
  apply chromatic_le_of_colorable G
  refine ⟨fun i => c (e.symm i), fun i j hij => hc _ _ ?_⟩
  simpa using hij

/-- With fewer than c neighbors, the missing vertex has a free color. -/
theorem colorable_of_delete_zero {h c : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (hc : FinColorable (G.comap Fin.succ) c)
    (hdeg : by classical exact G.degree 0 < c) : FinColorable G c := by
  classical
  obtain ⟨f, hf⟩ := hc
  let oldColor : Fin (h + 1) → Fin c := fun v =>
    if hv : v = 0 then (by have : 0 < c := lt_of_le_of_lt (Nat.zero_le _) hdeg; exact ⟨0, this⟩)
    else f (v.pred hv)
  let used : Finset (Fin c) := (G.neighborFinset 0).image oldColor
  have hused : used.card < c := (Finset.card_image_le).trans_lt hdeg
  obtain ⟨a, ha⟩ : ∃ a : Fin c, a ∉ used := by
    by_contra! hall
    have he : used = Finset.univ := Finset.eq_univ_of_forall hall
    have : used.card = c := by rw [he]; simp
    omega
  let color : Fin (h + 1) → Fin c := Fin.cases a f
  refine ⟨color, ?_⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero => exact (G.irrefl hij).elim
    | succ j =>
      change a ≠ f j
      intro he
      apply ha
      apply Finset.mem_image.mpr
      refine ⟨j.succ, (G.mem_neighborFinset 0 _).mpr hij, ?_⟩
      simpa [oldColor] using he.symm
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      change f i ≠ a
      intro he
      apply ha
      apply Finset.mem_image.mpr
      refine ⟨i.succ, (G.mem_neighborFinset 0 _).mpr hij.symm, ?_⟩
      simpa [oldColor] using he
    | succ j => exact hf i j hij

/-- Deleting a vertex of degree below chi-1 preserves the exact chromatic number. -/
theorem chromatic_delete_zero_eq {h : ℕ} (G : SimpleGraph (Fin (h + 1)))
    (hdeg : by classical exact G.degree 0 < ChromaticNumber G - 1) :
    ChromaticNumber (G.comap Fin.succ) = ChromaticNumber G := by
  apply le_antisymm (chromatic_comap_le G Fin.succ)
  by_contra! hlt
  have hcol : FinColorable (G.comap Fin.succ) (ChromaticNumber G - 1) :=
    (colorable_chromatic _).mono (by omega)
  have hc := chromatic_le_of_colorable G (colorable_of_delete_zero G hcol hdeg)
  have hp := chromatic_pos (Nat.succ_pos h) G
  omega

#assert_trust kernel colorable_of_delete_zero
#assert_trust kernel chromatic_delete_zero_eq
#print axioms chromatic_delete_zero_eq

end NLA.Proofs.SP12
