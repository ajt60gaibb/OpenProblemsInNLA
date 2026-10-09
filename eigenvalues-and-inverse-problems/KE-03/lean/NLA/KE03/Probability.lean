import NLA.KE03.Definitions
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Finite integer-grid anti-concentration for all rows simultaneously. -/

noncomputable section
open scoped BigOperators

namespace NLA.KE03

def GoodSeed {n : ℕ} (W : Mat n) (seed : Seed n) : Prop :=
  ∀ i, ‖W i‖ ≤ 2 * ‖(act W (seedVector seed)) i‖

theorem gridSize_pos (n : ℕ) : 0 < gridSize n := by
  exact pow_pos (by norm_num) _

theorem gridSize_bounds {n : ℕ} (hn : 0 < n) :
    1024 * n < gridSize n ∧ gridSize n ≤ 2048 * n := by
  constructor
  · exact Nat.lt_pow_succ_log_self (by norm_num) _
  · have h := Nat.pow_log_le_self 2 (x := 1024 * n) (by omega)
    dsimp [gridSize]
    rw [pow_succ]
    omega

private theorem integer_separation {N : ℕ} {a b : Fin N} (hab : a ≠ b) :
    1 ≤ ‖(a.val : ℂ) - (b.val : ℂ)‖ := by
  have hv : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have he : (a.val : ℂ) - (b.val : ℂ) = ((a.val : ℝ) - (b.val : ℝ) : ℝ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hv with h | h
  · have hc : (a.val : ℝ) + 1 ≤ b.val := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]
    linarith
  · have hc : (b.val : ℝ) + 1 ≤ a.val := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]
    linarith

private theorem row_difference {n N : ℕ} (w : Fin n → ℂ) (j : Fin n)
    (a b : Fin n → Fin N) (h : ∀ i, i ≠ j → a i = b i) :
    (∑ i, w i * ((a i).val : ℂ)) - (∑ i, w i * ((b i).val : ℂ)) =
      w j * (((a j).val : ℂ) - ((b j).val : ℂ)) := by
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single j]
  · ring
  · intro i _ hij
    rw [h i hij, sub_self]
  · simp

/-- A disk of radius half the largest coefficient contains at most one point
in every coordinate fiber of an integer grid. -/
theorem badRow_card_le {n N : ℕ} (hn : 0 < n) (w : Fin n → ℂ) :
    Fintype.card {b : Fin n → Fin N //
      ¬ ‖w‖ ≤ 2 * ‖∑ i, w i * ((b i).val : ℂ)‖} ≤ N ^ (n - 1) := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨j, hj⟩ := (IsGreatest.pi_norm w).1
  change ‖w j‖ = ‖w‖ at hj
  let f : {b : Fin n → Fin N // ¬ ‖w‖ ≤ 2 * ‖∑ i, w i * ((b i).val : ℂ)‖} →
      ({i : Fin n // i ≠ j} → Fin N) := fun b i => b.val i.val
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    funext i
    have hout : ∀ i, i ≠ j → a.val i = b.val i := by
      intro i hi
      exact congrFun hab ⟨i, hi⟩
    by_cases hij : i = j
    · subst i
      by_contra hne
      have hsep := integer_separation hne
      have ha := lt_of_not_ge a.property
      have hb := lt_of_not_ge b.property
      have hdiff := norm_sub_le (∑ i, w i * ((a.val i).val : ℂ))
        (∑ i, w i * ((b.val i).val : ℂ))
      rw [row_difference w j a.val b.val hout, norm_mul, hj] at hdiff
      have hmul := mul_le_mul_of_nonneg_left hsep (norm_nonneg w)
      nlinarith
    · exact hout i hij
  have hc : Fintype.card {i : Fin n // i ≠ j} = n - 1 := by
    simp [Fintype.card_subtype_compl]
  simpa [Fintype.card_fun, hc] using Fintype.card_le_of_injective f hf

theorem goodSeed_probability {n : ℕ} (hn : 0 < n) (W : Mat n) :
    (99 / 100 : ℝ) ≤ seedProbability n (GoodSeed W) := by
  classical
  let bad : Fin n → Finset (Seed n) := fun i =>
    Finset.univ.filter fun b => ¬ ‖W i‖ ≤ 2 * ‖(act W (seedVector b)) i‖
  have hb (i : Fin n) : (bad i).card ≤ gridSize n ^ (n - 1) := by
    have := badRow_card_le (N := gridSize n) hn (W i)
    simpa [bad, Fintype.card_subtype, act, seedVector,
      Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, dotProduct] using this
  have hunion : (Finset.univ.filter fun b : Seed n => ¬ GoodSeed W b) =
      Finset.univ.biUnion bad := by
    ext b
    simp [GoodSeed, bad]
  have hbad : Fintype.card {b : Seed n // ¬ GoodSeed W b} ≤
      n * gridSize n ^ (n - 1) := by
    rw [Fintype.card_subtype, hunion]
    exact Finset.card_biUnion_le.trans (by simpa using Finset.sum_le_sum (s := Finset.univ) fun i _ => hb i)
  have htotal : Fintype.card (Seed n) = gridSize n ^ n := by
    simp [Seed]
  have hsum : Fintype.card {b : Seed n // GoodSeed W b} +
      Fintype.card {b : Seed n // ¬ GoodSeed W b} = gridSize n ^ n := by
    rw [Fintype.card_subtype_compl, ← htotal]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have hpow : gridSize n ^ n = gridSize n ^ (n - 1) * gridSize n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hgrid := (gridSize_bounds hn).1
  have hnat : 99 * gridSize n ^ n ≤
      100 * Fintype.card {b : Seed n // GoodSeed W b} := by
    have hsmall : 100 * (n * gridSize n ^ (n - 1)) ≤ gridSize n ^ n := by
      rw [hpow]
      nlinarith
    omega
  dsimp [seedProbability]
  rw [htotal]
  have hpos : 0 < ((gridSize n ^ n : ℕ) : ℝ) := by
    exact_mod_cast pow_pos (gridSize_pos n) n
  apply (le_div_iff₀ hpos).2
  have hc : (99 : ℝ) * (gridSize n ^ n : ℕ) ≤
      100 * Fintype.card {b : Seed n // GoodSeed W b} := by exact_mod_cast hnat
  linarith

end NLA.KE03
