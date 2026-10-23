import NLA.Statements.TR14

/-! The final finite arithmetic of the block lower bound. This module combines
explicit block dimensions and additive inequalities; constructing the actual
blocks and proving these inequalities remain separate obligations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

open scoped BigOperators

/-- One large block supplies the binary lower bound; otherwise summing all
block inequalities supplies the local lower bound. Natural subtraction is
used only in the same guarded ranges as the final symmetric constructions. -/
theorem numerical_block_lower {m n r s R t : ℕ}
    (hm : 3 ≤ m) (hn : 2 ≤ n) (hrD : r ≤ m * (n - 1))
    (rblock Rblock : Fin t → ℕ)
    (hsumr : ∑ j, rblock j = r) (hsumR : ∑ j, Rblock j = R)
    (hts : t ≤ s)
    (hblock : ∀ j, m * min n (rblock j) + 2 ≤ Rblock j + rblock j + m) :
    min (m * (n - 1) - r + 2) ((m - 1) * r - (m - 2) * s) ≤ R := by
  classical
  by_cases hlarge : ∃ j, n ≤ rblock j
  · obtain ⟨j, hj⟩ := hlarge
    have hjr : rblock j ≤ r := by
      rw [← hsumr]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hjR : Rblock j ≤ R := by
      rw [← hsumR]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have hb := hblock j
    rw [min_eq_left hj] at hb
    have hD : m * (n - 1) + m = m * n := by
      calc
        m * (n - 1) + m = m * ((n - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = m * n := by congr 1; omega
    have hbound : m * (n - 1) - r + 2 ≤ R := by omega
    exact le_trans (min_le_left _ _) hbound
  · have hsmall : ∀ j, rblock j < n := by
      intro j
      exact Nat.lt_of_not_ge (fun hj => hlarge ⟨j, hj⟩)
    have hlocal (j : Fin t) : (m - 1) * rblock j ≤ Rblock j + (m - 2) := by
      have hb := hblock j
      rw [min_eq_right (Nat.le_of_lt (hsmall j))] at hb
      have hm1 : m = (m - 1) + 1 := by omega
      rw [hm1, Nat.add_mul, one_mul] at hb
      omega
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlocal j)
    have hsum' : (m - 1) * r ≤ R + (m - 2) * t := by
      simpa only [← Finset.mul_sum, Finset.sum_add_distrib, hsumr, hsumR,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_comm t (m - 2)] using hsum
    have hlocalbound : (m - 1) * r - (m - 2) * s ≤ R := by
      apply Nat.sub_le_iff_le_add.mpr
      have hts' := Nat.mul_le_mul_left (m - 2) hts
      omega
    exact le_trans (min_le_right _ _) hlocalbound

#assert_trust kernel numerical_block_lower
#print axioms numerical_block_lower

end NLA.Proofs.TR14
