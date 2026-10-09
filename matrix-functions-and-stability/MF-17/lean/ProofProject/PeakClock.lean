import ProofProject.GrowthRate
import ProofProject.SeparatedIntegers

/-!
# The clock of the separated finite-dimensional construction

The source peak time is `2 π² M N (1 + y²)`. The quadratic frequency
recurrence yields a linear bound for its double-logarithmic clock when
`N = r n` and `κ = n³`. The constant is explicit and no eventual qualifier
is needed beyond `n ≥ 1`.
-/

noncomputable section

namespace ProofProject

/-- The peak time associated to the source's choice of acceleration. -/
def peakTime (M : ℝ) (N : ℕ) (y : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * M * N * (1 + y ^ 2)

lemma peakTime_nonneg {M : ℝ} (hM : 0 ≤ M) (N : ℕ) (y : ℝ) :
    0 ≤ peakTime M N y := by
  unfold peakTime
  positivity

lemma peakTime_pos {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N) (y : ℝ) :
    0 < peakTime M N y := by
  unfold peakTime
  positivity

/-- A reusable estimate before tying the dimension to the construction index. -/
theorem separated_peakTime_clock_le {M : ℝ} (hM : 0 ≤ M) (N : ℕ)
    {κ : ℕ} (hκ : 1 ≤ κ) (p : ℕ → Bool) (j : ℕ) :
    growthLog (peakTime M N (separatedInteger κ p j)) ≤
      (j + 1 : ℕ) * Real.log 2 +
        Real.log (4 * Real.pi ^ 2 * M * N + Real.exp (Real.exp 1)) +
        Real.log 3 + Real.log (2 * (κ : ℝ)) := by
  let y : ℝ := separatedInteger κ p j
  let a : ℝ := 4 * Real.pi ^ 2 * M * N + Real.exp (Real.exp 1)
  let b : ℝ := Real.log 3 + Real.log (2 * (κ : ℝ))
  have hy : 2 ≤ y := by
    dsimp [y]
    exact_mod_cast two_le_separatedInteger hκ p j
  have hyp : 0 < y := by linarith
  have hE : 1 ≤ Real.exp (Real.exp 1) := Real.one_le_exp_iff.mpr (Real.exp_pos _).le
  have ha : 1 ≤ a := by
    dsimp [a]
    have : 0 ≤ 4 * Real.pi ^ 2 * M * (N : ℝ) := by positivity
    linarith
  have hapos : 0 < a := by linarith
  have hκr : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have hb : 0 < b := by
    have h₃ : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hk : 0 ≤ Real.log (2 * (κ : ℝ)) := Real.log_nonneg (by linarith)
    dsimp [b]
    linarith
  have hlogy : Real.log y ≤ (2 : ℝ) ^ j * b := separatedInteger_log_le hκ p j
  have htime : peakTime M N y + Real.exp (Real.exp 1) ≤ a * y ^ 2 := by
    have hq : 0 ≤ 2 * Real.pi ^ 2 * M * (N : ℝ) := by positivity
    have hqmul := mul_nonneg hq (show 0 ≤ y ^ 2 - 1 by nlinarith)
    have hEmul := mul_nonneg (Real.exp_pos (Real.exp 1)).le
      (show 0 ≤ y ^ 2 - 1 by nlinarith)
    dsimp [peakTime, a]
    nlinarith
  have hin := Real.log_le_log
    (growthLog_argument_pos (peakTime_nonneg hM N y)) htime
  rw [Real.log_mul hapos.ne' (pow_ne_zero _ hyp.ne'), Real.log_pow] at hin
  norm_num only [Nat.cast_ofNat] at hin
  have hpow : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
  have hla : 0 ≤ Real.log a := Real.log_nonneg ha
  have hin' : Real.log (peakTime M N y + Real.exp (Real.exp 1)) ≤
      2 ^ (j + 1) * (Real.log a + b) := by
    have hscale := mul_le_mul_of_nonneg_right hpow hla
    rw [pow_succ] at hscale ⊢
    nlinarith
  have hout := Real.log_le_log (growthLog_inner_pos (peakTime_nonneg hM N y)) hin'
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hout
  have hlast : Real.log (Real.log a + b) ≤ Real.log a + b :=
    Real.log_le_self (by positivity)
  change Real.log (Real.log (peakTime M N y + Real.exp (Real.exp 1))) ≤ _
  dsimp [a, b] at hout hlast ⊢
  linarith

/-- A constant depending only on the semigroup bound and replication number. -/
def peakClockConstant (M : ℝ) (r : ℕ) : ℝ :=
  r * Real.log 2 + Real.log (4 * Real.pi ^ 2 * M * r + Real.exp (Real.exp 1)) +
    Real.log 3 + Real.log 2 + 4

lemma peakClockConstant_pos {M : ℝ} (hM : 0 ≤ M) (r : ℕ) :
    0 < peakClockConstant M r := by
  have hE : 1 ≤ Real.exp (Real.exp 1) := Real.one_le_exp_iff.mpr (Real.exp_pos _).le
  have hc : 0 ≤ 4 * Real.pi ^ 2 * M * (r : ℝ) := by positivity
  have hD : 0 ≤ Real.log (4 * Real.pi ^ 2 * M * (r : ℝ) + Real.exp (Real.exp 1)) :=
    Real.log_nonneg (by linarith)
  have h₂ : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h₃ : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hr : 0 ≤ (r : ℝ) * Real.log 2 := mul_nonneg (Nat.cast_nonneg r) h₂
  unfold peakClockConstant
  linarith

/-- With `N = r n`, `κ = n³`, and the final (zero-based) frequency `N-1`,
the source witness time has clock bounded linearly in `n`. -/
theorem peakTime_clock_linear {M : ℝ} (hM : 0 ≤ M) {r n : ℕ}
    (hr : 1 ≤ r) (hn : 1 ≤ n) (p : ℕ → Bool) :
    growthLog (peakTime M (r * n) (separatedInteger (n ^ 3) p (r * n - 1))) ≤
      peakClockConstant M r * n := by
  have hκ : 1 ≤ n ^ 3 := one_le_pow₀ hn
  have h := separated_peakTime_clock_le hM (r * n) hκ p (r * n - 1)
  have hN : 1 ≤ r * n := by nlinarith
  have hindex : r * n - 1 + 1 = r * n := by omega
  rw [hindex] at h
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n : ℝ) := by linarith
  let D : ℝ := 4 * Real.pi ^ 2 * M * r + Real.exp (Real.exp 1)
  have hE : 1 ≤ Real.exp (Real.exp 1) := Real.one_le_exp_iff.mpr (Real.exp_pos _).le
  have hc : 0 ≤ 4 * Real.pi ^ 2 * M * (r : ℝ) := by positivity
  have hD : 1 ≤ D := by dsimp [D]; linarith
  have hDp : 0 < D := by linarith
  have harg : 4 * Real.pi ^ 2 * M * (r * n : ℕ) + Real.exp (Real.exp 1) ≤ D * n := by
    dsimp [D]
    push_cast
    have hm := mul_le_mul_of_nonneg_left hnr (Real.exp_pos (Real.exp 1)).le
    nlinarith
  have hlogarg := Real.log_le_log (by positivity :
    0 < 4 * Real.pi ^ 2 * M * (r * n : ℕ) + Real.exp (Real.exp 1)) harg
  rw [Real.log_mul hDp.ne' hnp.ne'] at hlogarg
  have hk : Real.log (2 * ((n ^ 3 : ℕ) : ℝ)) = Real.log 2 + 3 * Real.log (n : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hlogn : Real.log (n : ℝ) ≤ n := Real.log_le_self hnp.le
  have hconst : 0 ≤ Real.log D + Real.log 3 + Real.log 2 := by
    exact add_nonneg (add_nonneg (Real.log_nonneg hD)
      (Real.log_nonneg (by norm_num))) (Real.log_nonneg (by norm_num))
  have hscale := mul_le_mul_of_nonneg_left hnr hconst
  rw [hk] at h
  push_cast at h hlogarg
  dsimp [peakClockConstant]
  change _ ≤ ((r : ℝ) * Real.log 2 + Real.log D + Real.log 3 + Real.log 2 + 4) * n
  nlinarith

end ProofProject
