import NLA.TR13.UpperPolynomial

noncomputable section
open scoped BigOperators

namespace NLA.TR13

lemma hankel_of_moment_representation {m n r : ℕ} (h : Moments m n)
    (c t : Fin r → ℂ)
    (hc : ∀ i : Fin (m * (n - 1) + 1), h i = ∑ j, c j * t j ^ i.val) :
    VandermondeRankAtMost r (hankel h) := by
  refine ⟨c, fun _ => 1, t, ?_, ?_⟩
  · intro j he
    have hf := congrArg Prod.fst he
    norm_num at hf
  · ext i
    have hi : (∑ j : Fin m, (i j).val) < m * (n - 1) + 1 := by
      have hb : (∑ j : Fin m, (i j).val) ≤ m * (n - 1) := by
        calc
          (∑ j : Fin m, (i j).val) ≤ ∑ _j : Fin m, (n - 1) :=
            Finset.sum_le_sum (fun j _ => Nat.le_pred_of_lt (i j).isLt)
          _ = m * (n - 1) := by simp
      omega
    simpa [hankel, symmetricTensor, pureTensor, vandermondeVector,
      Finset.prod_pow_eq_pow_sum] using hc ⟨∑ j, (i j).val, hi⟩

/-- A nonempty principal Zariski-open set has actual Vandermonde decompositions
of the generic rank. This proves the complete upper bound in TR-13. -/
theorem generic_vandermonde_upper (m n : ℕ) (hm : 5 ≤ m) (_hodd : Odd m) (hn : 2 ≤ n) :
    ∃ p : MvPolynomial (Fin (m * (n - 1) + 1)) ℂ, p ≠ 0 ∧
      ∀ h : Moments m n, MvPolynomial.eval h p ≠ 0 →
        VandermondeRankAtMost (expectedRank m n) (hankel h) := by
  have hD : 5 ≤ m * (n - 1) := by
    have hnp : 1 ≤ n - 1 := by omega
    nlinarith
  have hr : 2 ≤ expectedRank m n := by unfold expectedRank; omega
  have hlo : 2 * expectedRank m n ≤ m * (n - 1) + 2 := by unfold expectedRank; omega
  have hhi : m * (n - 1) < 2 * expectedRank m n := by unfold expectedRank; omega
  obtain ⟨hp, hrep⟩ := generic_moment_representation hr hlo hhi
  refine ⟨upperPolynomial (m * (n - 1)) (expectedRank m n), hp, ?_⟩
  intro h hh
  obtain ⟨c, t, hc⟩ := hrep h hh
  exact hankel_of_moment_representation h c t hc

end NLA.TR13
