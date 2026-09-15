/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.
-/
import NLA.MF24.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

lemma length_flatten_replicate {α : Type*} (k : ℕ) (l : List α) :
    (List.replicate k l).flatten.length = k * l.length := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.replicate_succ, ih, Nat.succ_mul, Nat.add_comm]

lemma length_motif (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    (motif m t).length = m := by
  simp only [motif, List.length_cons, List.length_replicate]
  omega

lemma length_inverseBridges (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    (inverseBridges m t).length = (m - 1) * (m + 1) := by
  simp only [inverseBridges, length_flatten_replicate, List.length_cons,
    length_motif m hm t]

lemma dimension_eq (m : ℕ) : dimension m = m * stride m + 1 := by
  dsimp [dimension, stride]
  ring

lemma dimension_pos (m : ℕ) : 1 ≤ dimension m := by
  rw [dimension_eq]
  omega

lemma dimension_sub_one (m : ℕ) : dimension m - 1 = m * stride m := by
  rw [dimension_eq]
  omega

theorem family_dimensions (m : ℕ) (hm : 2 ≤ m) (t : ℝ) :
    1 ≤ dimension m ∧ dimension m = m * stride m + 1 ∧
    (sourceWordX m t).length = dimension m - 1 ∧
    (sourceWordY m t).length = dimension m - 1 := by
  have hm1 : 1 ≤ m := by omega
  have hs : m - 1 + 1 = m := Nat.sub_add_cancel hm1
  refine ⟨dimension_pos m, dimension_eq m, ?_, ?_⟩
  · rw [dimension_sub_one]
    simp only [sourceWordX, List.length_append, List.length_cons,
      List.length_nil, length_motif m hm1 t, length_inverseBridges m hm1 t]
    dsimp [stride]
    nlinarith
  · rw [dimension_sub_one]
    simp only [sourceWordY, List.length_append, List.length_cons,
      List.length_nil, length_motif m hm1 t, length_inverseBridges m hm1 t]
    dsimp [stride]
    nlinarith

#assert_trust kernel family_dimensions
#print axioms family_dimensions

end NLA.MF24
