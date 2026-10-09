import NLA.KE03.Search
import NLA.KE03.MatrixBounds
import Mathlib.Data.Nat.Choose.Sum

/-! The finite oracle transcript contains every vector used by the algorithm. -/

noncomputable section
open scoped BigOperators

namespace NLA.KE03

theorem history_head {n : ℕ} (A : Mat n) (b : Vec n) (m : ℕ) :
    (history (act A) b m).headD 0 = act (A ^ m) b := by
  induction m with
  | zero => simp [history]
  | succ m ih =>
    simp only [history, List.headD_cons, ih, pow_succ', act_mul, mul_apply_eq_comp]

theorem history_getD {n : ℕ} (A : Mat n) (b : Vec n) (m j : ℕ) (hj : j ≤ m) :
    (history (act A) b m).getD (m - j) 0 = act (A ^ j) b := by
  induction m generalizing j with
  | zero =>
    have : j = 0 := by omega
    subst j
    simp [history]
  | succ m ih =>
    by_cases htop : j = m + 1
    · subst j
      simp only [history, Nat.sub_self, List.getD_cons_zero]
      rw [history_head, pow_succ', act_mul, mul_apply_eq_comp]
    · have hjm : j ≤ m := by omega
      have hindex : m + 1 - j = (m - j) + 1 := by omega
      simpa only [history, hindex, List.getD_cons_succ] using ih j hjm

theorem act_sum {n : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Mat n) :
    act (∑ i ∈ S, f i) = ∑ i ∈ S, act (f i) := by
  exact map_sum Matrix.toEuclideanCLM _ _

theorem shiftedPower_history {n : ℕ} (A : Mat n) (b : Vec n) (m : ℕ) (s : ℂ) :
    shiftedPower (history (act A) b m) m s = act ((A + s • 1) ^ m) b := by
  have hc : Commute A (s • (1 : Mat n)) := by
    show A * (s • 1) = (s • 1) * A
    simp
  rw [hc.add_pow, act_sum]
  simp only [sum_apply, shiftedPower]
  apply Finset.sum_congr rfl
  intro j hj
  rw [history_getD A b m j (by have := Finset.mem_range.mp hj; omega)]
  have hterm : A ^ j * (s • (1 : Mat n)) ^ (m - j) * (m.choose j : Mat n) =
      ((m.choose j : ℂ) * s ^ (m - j)) • A ^ j := by
    rw [smul_pow, one_pow]
    have hn : (m.choose j : Mat n) = (m.choose j : ℂ) • (1 : Mat n) := by
      simp only [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_one]
    rw [hn]
    simp [smul_smul, mul_comm]
  rw [hterm, act_smul]
  rfl

end NLA.KE03
