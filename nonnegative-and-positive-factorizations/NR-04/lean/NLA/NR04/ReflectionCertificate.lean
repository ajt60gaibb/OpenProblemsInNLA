/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted formalization by agent /root/recover_published_coverage.

The exact upper certificate follows Section 5 of Matthew J. Colbrook's
NR-04 manuscript, retaining its prior Hrubeš / Gillis--Glineur reflection
construction attribution. The all-real scalar identity is proved symbolically;
there is no 81-entry numerical matrix-product test in this proof.
-/
import NLA.NR04.Numerical
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators

namespace NLA.NR04

/-- C02: the index shift cancels before taking the square. -/
theorem distance_index_semantics (i j : Fin 9) :
    distanceNine i j = (((i.val : ℝ) + 1) - ((j.val : ℝ) + 1)) ^ 2 := by
  dsimp [distanceNine]
  ring

/-- C03: only the nine exact one-coordinate labels require finite reduction. -/
theorem centered_labels (i : Fin 9) :
    label i ≤ 4 ∧ (label i : ℝ) = |center i| := by
  fin_cases i <;> norm_num [label, center]

/-- C04: all four sign cases, including zero at the shared boundaries. -/
theorem reflection_identity (s t : ℝ) :
    (|s| - |t|) ^ 2 + 4 * max s 0 * max (-t) 0 +
      4 * max (-s) 0 * max t 0 = (s - t) ^ 2 := by
  rcases le_total 0 s with hs | hs
  · rcases le_total 0 t with ht | ht
    · simp only [abs_of_nonneg hs, abs_of_nonneg ht, max_eq_left hs,
        max_eq_left ht, max_eq_right (neg_nonpos.mpr hs),
        max_eq_right (neg_nonpos.mpr ht)]
      ring
    · simp only [abs_of_nonneg hs, abs_of_nonpos ht, max_eq_left hs,
        max_eq_right ht, max_eq_right (neg_nonpos.mpr hs),
        max_eq_left (neg_nonneg.mpr ht)]
      ring
  · rcases le_total 0 t with ht | ht
    · simp only [abs_of_nonpos hs, abs_of_nonneg ht, max_eq_right hs,
        max_eq_left ht, max_eq_left (neg_nonneg.mpr hs),
        max_eq_right (neg_nonpos.mpr ht)]
      ring
    · simp only [abs_of_nonpos hs, abs_of_nonpos ht, max_eq_right hs,
        max_eq_right ht, max_eq_left (neg_nonneg.mpr hs),
        max_eq_left (neg_nonneg.mpr ht)]
      ring

private lemma selector_sum (i j : Fin 9) :
    (∑ r : Fin 5, (if label i = r.val then (1 : ℝ) else 0) *
      ((r.val : ℝ) - (label j : ℝ)) ^ 2) =
      ((label i : ℝ) - (label j : ℝ)) ^ 2 := by
  let a : Fin 5 := ⟨label i, Nat.lt_succ_iff.mpr (centered_labels i).1⟩
  rw [Finset.sum_eq_single a]
  · simp [a]
  · intro b _ hba
    have hlabel : label i ≠ b.val := by
      intro h
      apply hba
      exact Fin.ext h.symm
    simp [hlabel]
  · intro ha
    exact False.elim (ha (Finset.mem_univ a))

/-- C05: evaluate selectors once symbolically and apply the scalar identity. -/
theorem seven_factor_certificate :
    EntrywiseNonnegative upperW ∧ EntrywiseNonnegative upperH ∧
      upperW * upperH = distanceNine := by
  refine ⟨?_, ?_, ?_⟩
  · intro i r
    dsimp [upperW]
    split_ifs <;> positivity
  · intro r j
    dsimp [upperH]
    split_ifs <;> positivity
  · ext i j
    have hmain :
        (∑ r : Fin 5, upperW i (Fin.castAdd 2 r) * upperH (Fin.castAdd 2 r) j) =
          ((label i : ℝ) - (label j : ℝ)) ^ 2 := by
      calc
        _ = ∑ r : Fin 5, (if label i = r.val then (1 : ℝ) else 0) *
            ((r.val : ℝ) - (label j : ℝ)) ^ 2 := by
          apply Finset.sum_congr rfl
          intro r _
          simp [upperW, upperH, r.isLt]
        _ = _ := selector_sum i j
    have htail :
        (∑ r : Fin 2, upperW i (Fin.natAdd 5 r) * upperH (Fin.natAdd 5 r) j) =
          4 * max (center i) 0 * max (-center j) 0 +
            4 * max (-center i) 0 * max (center j) 0 := by
      rw [Fin.sum_univ_two]
      norm_num [upperW, upperH] <;> ring
    rw [Matrix.mul_apply, Fin.sum_univ_add (a := 5) (b := 2), hmain, htail]
    rw [(centered_labels i).2, (centered_labels j).2]
    calc
      _ = (center i - center j) ^ 2 := by
        simpa only [add_assoc] using reflection_identity (center i) (center j)
      _ = distanceNine i j := by
        dsimp [center, distanceNine]
        ring

/-- C07: the positivity of every off-diagonal squared distance is exact. -/
theorem distance_sign_pattern :
    EntrywiseNonnegative distanceNine ∧
      (∀ i, distanceNine i i = 0) ∧
      (∀ i j, i ≠ j → 0 < distanceNine i j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact sq_nonneg _
  · intro i
    simp [distanceNine]
  · intro i j hij
    have hval : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    have hreal : (i.val : ℝ) ≠ (j.val : ℝ) := by
      exact_mod_cast hval
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hreal)

#print axioms distance_index_semantics
#print axioms centered_labels
#print axioms reflection_identity
#print axioms seven_factor_certificate
#print axioms distance_sign_pattern
#assert_trust kernel distance_index_semantics
#assert_trust kernel centered_labels
#assert_trust kernel reflection_identity
#assert_trust kernel seven_factor_certificate
#assert_trust kernel distance_sign_pattern

end NLA.NR04
