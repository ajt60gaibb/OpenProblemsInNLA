/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Codex-assisted source draft by /root/pf03_final_referee2.

Exact frozen NR-04 C12 from Matthew J. Colbrook's mathematical proof,
University of Cambridge. The transpose branch treats nonsymmetric M correctly;
all natural inner dimensions k≤6, including zero, are quantified explicitly.
-/
import NLA.NR04.LowRankFactorObstruction
import NLA.NR04.SylvesterRank

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped Matrix

namespace NLA.NR04

theorem general_rank_seven_lower {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℝ) (hN : 9 ≤ N)
    (hrM : M.rank = 3) (hdiag : ∀ i, M i i = 0)
    (hoff : ∀ i j, i ≠ j → 0 < M i j) :
    ∀ k : ℕ, k ≤ 6 → ¬ HasNonnegativeFactorization M k := by
  intro k hk hfactor
  obtain ⟨W, H, hW, hH, hWH⟩ := hfactor
  have hrprod : (W * H).rank = 3 := by rw [hWH, hrM]
  rcases rank_three_small_factor W H hk hrprod with hrW | hrH
  · have hbound := low_rank_factor_obstruction M W H hk hW hH hWH hrM hrW hdiag hoff
    omega
  · have hHt : EntrywiseNonnegative Hᵀ := fun i j => hH j i
    have hWt : EntrywiseNonnegative Wᵀ := fun i j => hW j i
    have hprod : Hᵀ * Wᵀ = Mᵀ := by rw [← Matrix.transpose_mul, hWH]
    have hrMt : Mᵀ.rank = 3 := (Matrix.rank_transpose M).trans hrM
    have hrHt : Hᵀ.rank ≤ 4 := by simpa only [Matrix.rank_transpose] using hrH
    have hdt : ∀ i, Mᵀ i i = 0 := fun i => hdiag i
    have hot : ∀ i j, i ≠ j → 0 < Mᵀ i j := fun i j hij => hoff j i (Ne.symm hij)
    have hbound := low_rank_factor_obstruction Mᵀ Hᵀ Wᵀ hk hHt hWt hprod hrMt hrHt hdt hot
    omega

#print axioms general_rank_seven_lower
#assert_trust kernel general_rank_seven_lower

end NLA.NR04
