/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Original mathematical counterexample: Georg Maierhofer, University of Cambridge.

The source edge words act in reverse order in the transfer product. This
module establishes the exact family identity before any spectral inference.
-/
import NLA.MF24.Bridge
import NLA.MF24.Dimensions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF24

lemma transferProduct_append (u ρ : ℂ) (a b : List ℝ) :
    transferProduct u ρ (a ++ b) = transferProduct u ρ b * transferProduct u ρ a := by
  simp [transferProduct, List.reverse_append, List.map_append, List.prod_append]

lemma transferProduct_singleton (u ρ : ℂ) (w : ℝ) :
    transferProduct u ρ [w] = transferMatrix u ρ ((w : ℂ) ^ 2) := by
  simp [transferProduct]

lemma transferProduct_cons (u ρ : ℂ) (w : ℝ) (word : List ℝ) :
    transferProduct u ρ (w :: word) =
      transferProduct u ρ word * transferMatrix u ρ ((w : ℂ) ^ 2) := by
  change transferProduct u ρ ([w] ++ word) = _
  rw [transferProduct_append]
  simp [transferProduct]

lemma transferProduct_flatten_replicate (u ρ : ℂ) (word : List ℝ) (k : ℕ) :
    transferProduct u ρ (List.replicate k word).flatten = transferProduct u ρ word ^ k := by
  induction k with
  | zero => simp [transferProduct]
  | succ k ih =>
      rw [List.replicate_succ]
      change transferProduct u ρ (word ++ (List.replicate k word).flatten) = _
      rw [transferProduct_append, ih, pow_succ]

lemma transferProduct_inverseBridges (u ρ : ℂ) (m : ℕ) (t : ℝ) :
    transferProduct u ρ (inverseBridges m t) =
      (transferProduct u ρ (motif m t) * transferMatrix u ρ (((t⁻¹ : ℝ) : ℂ) ^ 2)) ^
        (m - 1) := by
  rw [inverseBridges, transferProduct_flatten_replicate, transferProduct_cons]

lemma family_transfer_value_eq (m : ℕ) (t : ℝ) (u ρ : ℂ) :
    transferValue u ρ (sourceWordX m t) = transferValue u ρ (sourceWordY m t) := by
  have hb := transfer_bridge (transferProduct u ρ (motif m t)) u ρ
    (((t⁻¹ : ℝ) : ℂ) ^ 2) 1 (m - 1)
  dsimp only at hb
  simp only [Matrix.mulVec_mulVec] at hb
  simp only [transferValue, sourceWordX, sourceWordY, transferProduct_append,
    transferProduct_inverseBridges]
  have hunit : transferProduct u ρ [1] = transferMatrix u ρ 1 := by
    simp [transferProduct]
  rw [hunit]
  simpa only [Matrix.mul_assoc] using hb

#assert_trust kernel family_transfer_value_eq
#print axioms family_transfer_value_eq

end NLA.MF24
