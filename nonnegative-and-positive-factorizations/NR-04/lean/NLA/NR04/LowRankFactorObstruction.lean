/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact frozen NR-04 C10 from Matthew J. Colbrook's mathematical proof,
University of Cambridge. Arbitrary factors are normalized internally, including
zero columns. No distinctness, positivity of W column sums, or stochasticity
is added to the original assumptions. C08 and C09 refer to the actual section.
-/
import NLA.NR04.FactorNormalization
import NLA.NR04.SmallSectionBound
import NLA.NR04.SectionContact

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Classical

namespace NLA.NR04

theorem low_rank_factor_obstruction {N k : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ)
    (W : Matrix (Fin N) (Fin k) ℝ) (H : Matrix (Fin k) (Fin N) ℝ)
    (hk : k ≤ 6) (hW : EntrywiseNonnegative W) (hH : EntrywiseNonnegative H)
    (hWH : W * H = M) (hrM : M.rank = 3) (hrW : W.rank ≤ 4)
    (hdiag : ∀ i, M i i = 0) (hoff : ∀ i j, i ≠ j → 0 < M i j) :
    N ≤ 8 := by
  have hN : 2 ≤ N := by
    have h := Matrix.rank_le_height M
    omega
  obtain ⟨hM, hs⟩ := sign_pattern_columnMass_positive M hN hdiag hoff
  obtain ⟨r, hr⟩ : ∃ r : Fin k, 0 < columnMass W r := by
    by_contra h
    have hs0 (r : Fin k) : columnMass W r = 0 := by
      apply le_antisymm _ (columnMass_nonnegative W hW r)
      exact le_of_not_gt (fun hr => h ⟨r, hr⟩)
    have hW0 : W = 0 := by
      ext i r
      exact column_zero_of_mass_zero W hW r (hs0 r) i
    have hM0 : M = 0 := by
      rw [← hWH, hW0, Matrix.zero_mul]
    rw [hM0, Matrix.rank_zero] at hrM
    omega
  let U := filledColumnNormalized W r
  let X := columnNormalized M
  have hU : ColumnStochastic U := filledColumnNormalized_stochastic W hW r hr
  have hX : ColumnStochastic X := columnNormalized_stochastic M hM hs
  have hrU : U.rank ≤ 4 := (filledColumnNormalized_rank_le W r).trans hrW
  have hrX : X.rank = 3 :=
    (columnNormalized_rank M (fun j => ne_of_gt (hs j))).trans hrM
  have hdX (i : Fin N) : X i i = 0 := by
    simp only [X, columnNormalized, hdiag i, zero_div]
  have hoX (i j : Fin N) (hij : i ≠ j) : 0 < X i j :=
    div_pos (hoff i j hij) (hs j)
  have hcontain : columnSet X ⊆ columnHull U :=
    normalized_factor_column_containment M W H hW hH hWH hs r
  have hup := (small_section_bound U X hk hU hX hrU hrX hcontain).2
  have hlow := (section_contact_bound U X hU hX hrX hdX hoX hcontain).2
  exact hlow.trans hup

#print axioms low_rank_factor_obstruction
#assert_trust kernel low_rank_factor_obstruction

end NLA.NR04
