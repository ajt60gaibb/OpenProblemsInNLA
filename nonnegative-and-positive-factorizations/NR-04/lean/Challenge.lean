import NLA.NR04.Definitions

set_option autoImplicit false

/-!
# NR-04 reference statements: draft awaiting two independent approvals

The fifteen `sorry` bodies below are intentional reference placeholders only.
No `Solution` exists in this packet. A future Solution must import the shared
transparent Definitions independently and must prove these same statements.
It must not import this Challenge or assume the geometric obligations.

Mathematical authorship: Matthew J. Colbrook, University of Cambridge.
Formalization contribution: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex-assisted.
-/

namespace NLA.NR04

/-- C01: the complete minimized kernel-mode LeanCert numerical obligation. -/
theorem minor_eight_positive : 0 < (8 : ℝ) := by
  sorry

/-- C02: zero-based indexing preserves the unchanged one-based target. -/
theorem distance_index_semantics (i j : Fin 9) :
    distanceNine i j = (((i.val : ℝ) + 1) - ((j.val : ℝ) + 1)) ^ 2 := by
  sorry

/-- C03: exact selector range and absolute-value semantics, including the center. -/
theorem centered_labels (i : Fin 9) :
    label i ≤ 4 ∧ (label i : ℝ) = |center i| := by
  sorry

/-- C04: the reflection identity over all reals, not just a tested finite list. -/
theorem reflection_identity (s t : ℝ) :
    (|s| - |t|) ^ 2 + 4 * max s 0 * max (-t) 0 +
      4 * max (-s) 0 * max t 0 = (s - t) ^ 2 := by
  sorry

/-- C05: the explicit seven-term upper certificate for the actual matrix. -/
theorem seven_factor_certificate :
    EntrywiseNonnegative upperW ∧ EntrywiseNonnegative upperH ∧
      upperW * upperH = distanceNine := by
  sorry

/-- C06: exact determinant and ordinary rank, with the nonzero minor consumed. -/
theorem distance_rank_certificate :
    (distanceNine.submatrix firstThree firstThree).det = 8 ∧
      distanceNine.rank = 3 := by
  sorry

/-- C07: no off-diagonal zero or strict-positivity exception is discarded. -/
theorem distance_sign_pattern :
    EntrywiseNonnegative distanceNine ∧
      (∀ i, distanceNine i i = 0) ∧
      (∀ i j, i ≠ j → 0 < distanceNine i j) := by
  sorry

/-- C08: actual finite extreme-point count of the two-dimensional section.
The proof must supply the three-polytope facet bound internally. -/
theorem small_section_bound {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hk : k ≤ 6) (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrU : U.rank ≤ 4) (hrX : X.rank = 3)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      ((columnSection U X).extremePoints ℝ).ncard ≤ 8 := by
  sorry

/-- C09: the source polygon-contact argument, in precisely its needed setting.
There is no restriction on the number or ordinary rank of the outer generators. -/
theorem section_contact_bound {N k : ℕ}
    (U : Matrix (Fin N) (Fin k) ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hU : ColumnStochastic U) (hX : ColumnStochastic X)
    (hrX : X.rank = 3) (hdiag : ∀ i, X i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < X i j)
    (hcontain : columnSet X ⊆ columnHull U) :
    ((columnSection U X).extremePoints ℝ).Finite ∧
      N ≤ ((columnSection U X).extremePoints ℝ).ncard := by
  sorry

/-- C10: manuscript Lemma 3 for arbitrary unnormalized nonnegative factors.
Zero columns of W and all smaller inner dimensions remain allowed. -/
theorem low_rank_factor_obstruction {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ)
    (W : Matrix (Fin N) (Fin k) ℝ) (H : Matrix (Fin k) (Fin N) ℝ)
    (hk : k ≤ 6) (hW : EntrywiseNonnegative W) (hH : EntrywiseNonnegative H)
    (hWH : W * H = M) (hrM : M.rank = 3) (hrW : W.rank ≤ 4)
    (hdiag : ∀ i, M i i = 0) (hoff : ∀ i j, i ≠ j → 0 < M i j) :
    N ≤ 8 := by
  sorry

/-- C11: the genuine Sylvester/rank-nullity consequence used in the contradiction. -/
theorem rank_three_small_factor {m n k : ℕ}
    (W : Matrix (Fin m) (Fin k) ℝ) (H : Matrix (Fin k) (Fin n) ℝ)
    (hk : k ≤ 6) (hr : (W * H).rank = 3) :
    W.rank ≤ 4 ∨ H.rank ≤ 4 := by
  sorry

/-- C12: manuscript Theorem 4, including nonsymmetric matrices and every k ≤ 6. -/
theorem general_rank_seven_lower {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hN : 9 ≤ N)
    (hrM : M.rank = 3) (hdiag : ∀ i, M i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < M i j) :
    ∀ k : ℕ, k ≤ 6 → ¬ HasNonnegativeFactorization M k := by
  sorry

/-- C13: the actual distance matrix excludes every smaller width, including zero. -/
theorem nine_point_no_small_factor :
    ∀ k : ℕ, k ≤ 6 → ¬ HasNonnegativeFactorization distanceNine k := by
  sorry

/-- C14: seven is the minimum feasible real nonnegative factorization width. -/
theorem nine_point_nonnegative_rank_seven :
    IsLeast {k : ℕ | HasNonnegativeFactorization distanceNine k} 7 := by
  sorry

/-- C15: the original question, with both arbitrary real factor matrices explicit. -/
theorem canonical_six_factor_impossible :
    ¬ ∃ W : Matrix (Fin 9) (Fin 6) ℝ,
      ∃ H : Matrix (Fin 6) (Fin 9) ℝ,
        (∀ i j, 0 ≤ W i j) ∧ (∀ i j, 0 ≤ H i j) ∧
          W * H = distanceNine := by
  sorry

end NLA.NR04
