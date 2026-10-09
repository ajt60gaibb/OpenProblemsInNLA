import NLA.KE03.Search
import NLA.KE03.Probability

/-! An explicit universal worst-case bound for the number of oracle calls. -/

noncomputable section
namespace NLA.KE03

theorem distortion_ge_one {n : ℕ} (hn : 0 < n) {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ distortion n K := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hN1 : (1 : ℝ) ≤ gridSize n := by exact_mod_cast gridSize_pos n
  dsimp [distortion]
  nlinarith [mul_le_mul hn1 hN1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity : (0 : ℝ) ≤ n)]

theorem distortion_log_bound {n : ℕ} (hn : 0 < n) {K : ℝ} (hK : 1 ≤ K) :
    Real.log (distortion n K) ≤ 12 * (1 + Real.log ((n : ℝ) * K)) := by
  let x : ℝ := n * K
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : 1 ≤ x := by dsimp [x]; nlinarith
  have hxpos : 0 < x := by linarith
  have hnx : (n : ℝ) ≤ x := by dsimp [x]; nlinarith
  have hN : (gridSize n : ℝ) ≤ 2048 * n := by
    exact_mod_cast (gridSize_bounds hn).2
  have hF : distortion n K ≤ 4096 * x ^ 2 := by
    have he : distortion n K = 2 * gridSize n * x := by dsimp [distortion, x]; ring
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hN hxpos.le,
      mul_le_mul_of_nonneg_right hnx hxpos.le]
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hc : Real.log (4096 : ℝ) ≤ 12 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at *
    linarith
  calc
    Real.log (distortion n K) ≤ Real.log (4096 * x ^ 2) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (distortion_ge_one hn hK)) hF
    _ = Real.log 4096 + 2 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_ne_zero _ hxpos.ne'), Real.log_pow]
      norm_num
    _ ≤ 12 * (1 + Real.log ((n : ℝ) * K)) := by change _ ≤ 12 * (1 + Real.log x); linarith

theorem eta_log_lower {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    eta ε / 2 ≤ Real.log (1 + eta ε) := by
  have hη := eta_pos hε
  have hη1 : eta ε ≤ 1 := by dsimp [eta]; nlinarith
  have hlog := Real.le_log_one_add_of_nonneg hη.le
  have hsmall : eta ε / 2 ≤ 2 * eta ε / (eta ε + 2) := by
    apply (le_div_iff₀ (by linarith)).2
    nlinarith
  exact hsmall.trans hlog

theorem degreeSearch_query_bound {n m : ℕ} (hn : 0 < n) {K ε : ℝ}
    (hK : 1 ≤ K) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hm : m ∈ degreeSearch n K ε) :
    (m : ℝ) ≤ queryBound 32768 n K ε := by
  rcases (Part.mem_map_iff _).mp hm with ⟨k, hk, rfl⟩
  have hη := eta_pos hε
  have hbase : 0 < 1 + eta ε := by linarith
  have hlog : (k : ℝ) * Real.log (1 + eta ε) ≤ Real.log (distortion n K) := by
    by_cases hk0 : k = 0
    · simp [hk0, Real.log_nonneg (distortion_ge_one hn hK)]
    · have hmin := searchNat_min hk (j := k - 1) (by omega)
      have hpow : (1 + eta ε) ^ k < distortion n K := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k), not_le] using hmin
      have hl := Real.log_le_log (pow_pos hbase k) hpow.le
      rwa [Real.log_pow] at hl
  have hloglow := mul_le_mul_of_nonneg_left (eta_log_lower hε hεhalf)
    (show 0 ≤ (k : ℝ) by positivity)
  have hlogupper := distortion_log_bound hn hK
  have hdegree : (k : ℝ) * ε ^ 2 ≤ 24576 * (1 + Real.log ((n : ℝ) * K)) := by
    dsimp [eta] at hloglow hlog
    linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx1 : 1 ≤ (n : ℝ) * K := by nlinarith
  have hL : 1 ≤ 1 + Real.log ((n : ℝ) * K) := by linarith [Real.log_nonneg hx1]
  have heps : ε ^ 2 < 1 := by nlinarith
  dsimp [queryBound]
  apply (le_div_iff₀ (sq_pos_of_pos hε)).2
  push_cast
  nlinarith

end NLA.KE03
