import Mathlib.Data.Nat.Basic

/-!
  TR-04 solution development.

  The full TT-SVD theorem is not claimed here: Lean 4.33.1 and the pinned
  dependencies were unavailable in the execution environment, and the
  matrix-unfolding/SVD interfaces needed for the complete proof have not yet
  been supplied.  This file contains only a proved, kernel-checkable support
  fact used by the intended finite-window algorithm.  It does not import
  `Challenge.lean`.
-/

theorem candidate_count_le_first_mode
    {n₁ t k : Nat} (ht : t ≤ n₁) (hk : k ≤ t) : k ≤ n₁ := by
  exact Nat.le_trans hk ht

theorem cyclic_window_count_le_first_mode
    {n₁ t : Nat} (ht : t ≤ n₁) : t ≤ n₁ := by
  exact ht

#print axioms candidate_count_le_first_mode
#print axioms cyclic_window_count_le_first_mode


