/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Finite-set separation for the planar part of Matthew J. Colbrook's NR-04
argument, University of Cambridge. No cyclic order or vertex bound is assumed.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.NR04

/-- The first coordinate of the actual shear `(x,y) ↦ (x+t*y,y)`. -/
def planeFirst (t : ℝ) (p : Fin 2 → ℝ) : ℝ := p 0 + t * p 1

/-- One finite set of excluded real parameters suffices to separate a finite
injective plane family. Equal second coordinates are handled without division. -/
theorem finite_plane_family_separating_coordinate {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (hw : Function.Injective w) :
    ∃ t : ℝ, Function.Injective (fun i => planeFirst t (w i)) := by
  classical
  let bad : Fin n × Fin n → ℝ := fun ij =>
    (w ij.2 0 - w ij.1 0) / (w ij.1 1 - w ij.2 1)
  obtain ⟨t, ht⟩ := (Set.finite_range bad).exists_notMem
  refine ⟨t, ?_⟩
  intro i j hij
  by_contra hne
  have hy : w i 1 ≠ w j 1 := by
    intro heq
    have hx : w i 0 = w j 0 := by
      change w i 0 + t * w i 1 = w j 0 + t * w j 1 at hij
      rw [heq] at hij
      linarith only [hij]
    have hpoints : w i = w j := by
      funext k
      fin_cases k
      · exact hx
      · exact heq
    exact hne (hw hpoints)
  have htbad : t = bad (i, j) := by
    dsimp [bad]
    apply (eq_div_iff (sub_ne_zero.mpr hy)).mpr
    change w i 0 + t * w i 1 = w j 0 + t * w j 1 at hij
    nlinarith only [hij]
  exact ht ⟨(i, j), htbad.symm⟩

/-- A separated finite nonempty family has a strict, hence unique, minimum
of the selected real coordinate. -/
theorem separated_plane_family_strict_minimum {n : ℕ}
    (w : Fin n → Fin 2 → ℝ) (t : ℝ)
    (hsep : Function.Injective (fun i => planeFirst t (w i)))
    (hn : 0 < n) :
    ∃ i0 : Fin n, ∀ i : Fin n, i ≠ i0 →
      planeFirst t (w i0) < planeFirst t (w i) := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i0, _, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun i => planeFirst t (w i)) hnonempty
  refine ⟨i0, ?_⟩
  intro i hi
  apply lt_of_le_of_ne (hmin i (Finset.mem_univ _))
  intro heq
  exact hi (hsep heq).symm

#print axioms finite_plane_family_separating_coordinate
#print axioms separated_plane_family_strict_minimum
#assert_trust kernel finite_plane_family_separating_coordinate
#assert_trust kernel separated_plane_family_strict_minimum

end NLA.NR04
