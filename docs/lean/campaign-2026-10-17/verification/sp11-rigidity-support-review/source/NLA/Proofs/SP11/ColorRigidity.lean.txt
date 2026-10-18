import NLA.Proofs.SP11.HistogramRigidity
import NLA.Proofs.SP11.ColorBounds
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Classwise recovery of conduit colors

The induction separates shared vertex classes. Lower-label children are fixed
before a class is examined, so equal incident-color sums become equal sums of
output colors. Earlier blockers or a tie to an earlier output give the local
lower bounds. This module states all needed finite shape data explicitly.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.SP11

variable {O : Type*} [Fintype O] {n : ℕ}

/-- Recover every output from equality of incident-color totals, class by class.
The local reconstruction premise must be proved from the actual garden shape. -/
theorem color_eq_of_class_incident_sums
    (label : O → Fin n) (Children : O → Type*) [∀ o, Fintype (Children o)]
    (child : (o : O) → Children o → O)
    (hchild : ∀ o s, label (child o s) < label o)
    (best actual : O → ℕ)
    (hsum : ∀ u : Fin n,
      (∑ o ∈ Finset.univ.filter (fun o => label o = u),
        (actual o + ∑ s : Children o, actual (child o s))) =
      ∑ o ∈ Finset.univ.filter (fun o => label o = u),
        (best o + ∑ s : Children o, best (child o s)))
    (hstep : ∀ o,
      (∀ p, label p < label o → actual p = best p) → best o ≤ actual o) :
    actual = best := by
  classical
  have recover (u : Fin n) : ∀ o, label o = u → actual o = best o := by
    induction u using (measure (fun u : Fin n => u.val)).wf.induction with
    | h u ih =>
      have hearly (p : O) (hp : label p < u) : actual p = best p :=
        ih (label p) hp p rfl
      let S : Finset O := Finset.univ.filter (fun o => label o = u)
      have hlow (o : O) (ho : o ∈ S) : best o ≤ actual o := by
        have hlu : label o = u := (Finset.mem_filter.mp ho).2
        apply hstep o
        intro p hp
        exact hearly p (by simpa only [hlu] using hp)
      have hchildren :
          (∑ o ∈ S, ∑ s : Children o, actual (child o s)) =
            ∑ o ∈ S, ∑ s : Children o, best (child o s) := by
        apply Finset.sum_congr rfl
        intro o ho
        have hlu : label o = u := (Finset.mem_filter.mp ho).2
        apply Finset.sum_congr rfl
        intro s _
        exact hearly (child o s) (by simpa only [hlu] using hchild o s)
      have ht := hsum u
      change (∑ o ∈ S, (actual o + ∑ s : Children o, actual (child o s))) =
        ∑ o ∈ S, (best o + ∑ s : Children o, best (child o s)) at ht
      simp only [Finset.sum_add_distrib] at ht
      have hout : (∑ o ∈ S, best o) = ∑ o ∈ S, actual o := by omega
      have heq := (Finset.sum_eq_sum_iff_of_le hlow).mp hout
      intro o ho
      exact (heq o (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩)).symm
  funext o
  exact recover (label o) o rfl

/-- Explicit local shape conditions sufficient for the class induction. Every
output is either tied to an earlier class or blocked at every smaller color
by an earlier-class conduit with that canonical color. -/
theorem color_eq_of_class_incident_sums_and_blockers
    (label : O → Fin n) (Children : O → Type*) [∀ o, Fintype (Children o)]
    (child : (o : O) → Children o → O)
    (hchild : ∀ o s, label (child o s) < label o)
    (best actual : O → ℕ)
    (hsum : ∀ u : Fin n,
      (∑ o ∈ Finset.univ.filter (fun o => label o = u),
        (actual o + ∑ s : Children o, actual (child o s))) =
      ∑ o ∈ Finset.univ.filter (fun o => label o = u),
        (best o + ∑ s : Children o, best (child o s)))
    (hshape : ∀ o,
      (∃ p, label p < label o ∧ actual o = actual p ∧ best o = best p) ∨
      (∀ q : ℕ, q < best o →
        ∃ p, label p < label o ∧ best p = q ∧ actual o ≠ actual p)) :
    actual = best := by
  apply color_eq_of_class_incident_sums label Children child hchild best actual hsum
  intro o hearly
  rcases hshape o with ⟨p, hp, hactual, hbest⟩ | hblock
  · rw [hactual, hearly p hp, hbest]
  · by_contra hnot
    have hlt : actual o < best o := Nat.lt_of_not_ge hnot
    obtain ⟨p, hp, hbest, hne⟩ := hblock (actual o) hlt
    exact hne ((hearly p hp).trans hbest).symm

#assert_trust kernel color_eq_of_class_incident_sums
#assert_trust kernel color_eq_of_class_incident_sums_and_blockers
#print axioms color_eq_of_class_incident_sums_and_blockers

end NLA.Proofs.SP11
