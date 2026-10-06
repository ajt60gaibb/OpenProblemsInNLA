import Mathlib
import LeanCert.Tactic.Verification

/-! Deterministic scalar recursion used by the reviewed Gaussian spectral
induction. No probabilistic source estimate is assumed or proved here. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.IE06.ScalarRecurrence

def step (ℓ : ℝ) (d : ℕ) : ℕ :=
  max (100 * d) ⌈(d : ℝ) ^ 2 / ℓ⌉₊

def orbit (ℓ : ℝ) (d : ℕ) : ℕ → ℕ
  | 0 => d
  | i + 1 => step ℓ (orbit ℓ d i)

def cost (n : ℕ) (ℓ : ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    if orbit ℓ d i < n then 1 + ℓ / (orbit ℓ d i : ℝ) else 0

theorem step_ge_linear (ℓ : ℝ) (d : ℕ) : 100 * d ≤ step ℓ d :=
  le_max_left _ _

theorem step_ge_self (ℓ : ℝ) (d : ℕ) : d ≤ step ℓ d := by
  have := step_ge_linear ℓ d
  omega

theorem step_pos (ℓ : ℝ) {d : ℕ} (hd : 0 < d) : 0 < step ℓ d :=
  lt_of_lt_of_le hd (step_ge_self ℓ d)

theorem step_monotone {ℓ : ℝ} (hℓ : 0 < ℓ) : Monotone (step ℓ) := by
  intro d e hde
  apply max_le_max
  · exact Nat.mul_le_mul_left _ hde
  · apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (sq_le_sq₀ (Nat.cast_nonneg d) (Nat.cast_nonneg e) |>.2 (by exact_mod_cast hde))
      hℓ.le

theorem step_ge_quadratic {ℓ : ℝ} (_hℓ : 0 < ℓ) (d : ℕ) :
    (d : ℝ) ^ 2 / ℓ ≤ (step ℓ d : ℝ) := by
  exact (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right _ _))

theorem orbit_ge_start (ℓ : ℝ) (d i : ℕ) : d ≤ orbit ℓ d i := by
  induction i with
  | zero => rfl
  | succ i ih => exact ih.trans (step_ge_self ℓ _)

theorem orbit_pos (ℓ : ℝ) {d : ℕ} (hd : 0 < d) (i : ℕ) : 0 < orbit ℓ d i :=
  lt_of_lt_of_le hd (orbit_ge_start ℓ d i)

theorem orbit_monotone_start {ℓ : ℝ} (hℓ : 0 < ℓ) (i : ℕ) :
    Monotone (fun d => orbit ℓ d i) := by
  intro d e hde
  induction i with
  | zero => exact hde
  | succ i ih => exact step_monotone hℓ ih

theorem orbit_monotone_index (ℓ : ℝ) (d : ℕ) : Monotone (orbit ℓ d) :=
  monotone_nat_of_le_succ (fun _i => step_ge_self ℓ _)

theorem orbit_shift (ℓ : ℝ) (d i : ℕ) :
    orbit ℓ d (i+1) = orbit ℓ (step ℓ d) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change step ℓ (orbit ℓ d (i+1)) = step ℓ (orbit ℓ (step ℓ d) i)
      rw [ih]

theorem orbit_add (ℓ : ℝ) (d i j : ℕ) :
    orbit ℓ d (i+j) = orbit ℓ (orbit ℓ d i) j := by
  induction j with
  | zero => simp [orbit]
  | succ j ih =>
      change step ℓ (orbit ℓ d (i+j)) = step ℓ (orbit ℓ (orbit ℓ d i) j)
      rw [ih]

theorem orbit_ge_geometric (ℓ : ℝ) (d i : ℕ) :
    100 ^ i * d ≤ orbit ℓ d i := by
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
      have h := (Nat.mul_le_mul_left 100 ih).trans
        (step_ge_linear ℓ (orbit ℓ d i))
      simpa [orbit, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h

theorem orbit_ge_add (ℓ : ℝ) {d : ℕ} (hd : 0 < d) (i : ℕ) :
    d + i ≤ orbit ℓ d i := by
  induction i with
  | zero => simp [orbit]
  | succ i ih =>
      have hp := orbit_pos ℓ hd i
      have hs := step_ge_linear ℓ (orbit ℓ d i)
      change d + (i+1) ≤ step ℓ (orbit ℓ d i)
      omega

theorem orbit_terminated (n : ℕ) (ℓ : ℝ) {d : ℕ} (hd : 0 < d) :
    n ≤ orbit ℓ d n := by
  have := orbit_ge_add ℓ hd n
  omega

theorem cost_zero_of_ge (n : ℕ) (ℓ : ℝ) {d : ℕ} (hd : n ≤ d) :
    cost n ℓ d = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp only [not_lt.mpr (hd.trans (orbit_ge_start ℓ d i)), ↓reduceIte]

theorem cost_antitone {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {d e : ℕ}
    (hd : 0 < d) (hde : d ≤ e) : cost n ℓ e ≤ cost n ℓ d := by
  apply Finset.sum_le_sum
  intro i hi
  have hmono := orbit_monotone_start hℓ i hde
  have hp : (0 : ℝ) < orbit ℓ d i := by exact_mod_cast orbit_pos ℓ hd i
  by_cases he : orbit ℓ e i < n
  · have hd' : orbit ℓ d i < n := lt_of_le_of_lt hmono he
    simp only [he, hd', ↓reduceIte]
    have hmR : (orbit ℓ d i : ℝ) ≤ orbit ℓ e i := Nat.cast_le.mpr hmono
    exact add_le_add le_rfl (div_le_div_of_nonneg_left hℓ.le hp hmR)
  · simp only [he, ↓reduceIte]
    split_ifs <;> positivity

theorem cost_recurrence {n d : ℕ} (ℓ : ℝ) (hd : 0 < d) (hdn : d < n) :
    cost n ℓ d = 1 + ℓ / d + cost n ℓ (step ℓ d) := by
  let f : ℕ → ℝ := fun i =>
    if orbit ℓ d i < n then 1 + ℓ / (orbit ℓ d i : ℝ) else 0
  have hend : f n = 0 := by
    simp [f, not_lt.mpr (orbit_terminated n ℓ hd)]
  have hsum := Finset.sum_range_succ' f n
  rw [Finset.sum_range_succ, hend, add_zero] at hsum
  change (∑ i ∈ Finset.range n, f i) = _
  rw [hsum]
  have hshift : (∑ i ∈ Finset.range n, f (i+1)) = cost n ℓ (step ℓ d) := by
    simp only [f, orbit_shift, cost]
  rw [hshift]
  simp only [f, orbit, hdn, ↓reduceIte]
  ring

theorem reciprocal_sum_le (ℓ : ℝ) (hℓ : 0 ≤ ℓ) (m : ℕ) :
    ∀ d : ℕ, 0 < d →
    (∑ i ∈ Finset.range m, ℓ / (orbit ℓ d i : ℝ)) ≤ 2 * ℓ / d := by
  induction m with
  | zero =>
      intro d hd
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ m ih =>
      intro d hd
      rw [Finset.sum_range_succ']
      simp_rw [orbit_shift]
      change (∑ i ∈ Finset.range m, ℓ / (orbit ℓ (step ℓ d) i : ℝ)) + ℓ / d ≤ _
      have hi := ih (step ℓ d) (step_pos ℓ hd)
      have hdR : (0 : ℝ) < d := by exact_mod_cast hd
      have hsR : (0 : ℝ) < step ℓ d := by exact_mod_cast step_pos ℓ hd
      have htwo : (2 : ℝ) * d ≤ step ℓ d := by
        have := step_ge_linear ℓ d
        have : 2*d ≤ step ℓ d := by omega
        exact_mod_cast this
      have hdiv : 2 * ℓ / (step ℓ d : ℝ) ≤ ℓ / d := by
        apply (div_le_div_iff₀ hsR hdR).2
        nlinarith
      calc
        (∑ i ∈ Finset.range m, ℓ / (orbit ℓ (step ℓ d) i : ℝ)) + ℓ / d
            ≤ 2 * ℓ / (step ℓ d : ℝ) + ℓ / d := add_le_add hi le_rfl
        _ ≤ ℓ / d + ℓ / d := add_le_add hdiv le_rfl
        _ = 2 * ℓ / d := by ring


theorem hundred_mul_le_pow {j : ℕ} (hj : 1 ≤ j) : 100*j ≤ 100^j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      rw [pow_succ]
      nlinarith

theorem sq_le_two_pow {j : ℕ} (hj : 4 ≤ j) : j^2 ≤ 2^j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
      rw [show 2^(j+1) = 2^j*2 from pow_succ 2 j]
      have hmul := Nat.mul_le_mul_left j hj
      nlinarith

theorem quadratic_orbit_lower {ℓ : ℝ} (hℓ : 0 < ℓ) {d : ℕ}
    (hd : 100*ℓ ≤ (d : ℝ)) (i : ℕ) :
    ℓ * (100 : ℝ)^(2^i) ≤ (orbit ℓ d i : ℝ) := by
  induction i with
  | zero => simpa [orbit, mul_comm] using hd
  | succ i ih =>
      have hnonneg : 0 ≤ ℓ * (100 : ℝ)^(2^i) := by positivity
      have hsq : (ℓ * (100 : ℝ)^(2^i))^2 ≤ (orbit ℓ d i : ℝ)^2 :=
        (sq_le_sq₀ hnonneg (Nat.cast_nonneg _)).2 ih
      have hnext := step_ge_quadratic hℓ (orbit ℓ d i)
      have heq : ℓ * (100 : ℝ)^(2^(i+1)) =
          (ℓ * (100 : ℝ)^(2^i))^2 / ℓ := by
        rw [show 2^(i+1) = 2^i*2 from pow_succ 2 i, pow_mul]
        field_simp
      change ℓ * (100 : ℝ)^(2^(i+1)) ≤ (step ℓ (orbit ℓ d i) : ℝ)
      rw [heq]
      exact (div_le_div_of_nonneg_right hsq hℓ.le).trans hnext

theorem stopped_count_le {n d m : ℕ} (ℓ : ℝ)
    (hm : n ≤ orbit ℓ d m) :
    ((Finset.range n).filter (fun i => orbit ℓ d i < n)).card ≤ m := by
  calc
    ((Finset.range n).filter (fun i => orbit ℓ d i < n)).card ≤
        (Finset.range m).card := by
      apply Finset.card_le_card
      intro i hi
      have hi' := (Finset.mem_filter.mp hi).2
      apply Finset.mem_range.mpr
      by_contra h
      have := hm.trans (orbit_monotone_index ℓ d (le_of_not_gt h))
      omega
    _ = m := Finset.card_range m

theorem cost_le_count_and_reciprocal {n d m : ℕ} (ℓ : ℝ)
    (hℓ : 0 ≤ ℓ) (hd : 0 < d) (hm : n ≤ orbit ℓ d m) :
    cost n ℓ d ≤ (m : ℝ) + 2*ℓ/d := by
  have hterm : cost n ℓ d ≤
      (∑ i ∈ Finset.range n, if orbit ℓ d i < n then (1 : ℝ) else 0) +
      ∑ i ∈ Finset.range n, ℓ / (orbit ℓ d i : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : orbit ℓ d i < n
    · simp only [h, ↓reduceIte]
      exact le_rfl
    · simp only [h, ↓reduceIte, zero_add]
      positivity
  rw [Finset.sum_boole] at hterm
  exact hterm.trans (add_le_add
    (by exact_mod_cast stopped_count_le ℓ hm)
    (reciprocal_sum_le ℓ hℓ n d hd))

/-- Two blocks of ceil(sqrt(log n)) iterations suffice. The conclusion
is a symbolic bound for every n satisfying the stated logarithm bound. -/
theorem orbit_reaches_dimension {n d : ℕ} (hn : 0 < n)
    (hlog : 256 ≤ Real.log (n : ℝ))
    (hd : ⌈Real.sqrt (Real.log (n : ℝ))⌉₊ ≤ d) :
    n ≤ orbit (Real.log (n : ℝ)) d
      (2 * ⌈Real.sqrt (Real.log (n : ℝ))⌉₊) := by
  let ℓ := Real.log (n : ℝ)
  let J : ℕ := ⌈Real.sqrt ℓ⌉₊
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  have hJsqrt : Real.sqrt ℓ ≤ (J : ℝ) := Nat.le_ceil _
  have hJ16 : 16 ≤ J := by
    have hs : (16 : ℝ) ≤ Real.sqrt ℓ :=
      (Real.le_sqrt (by norm_num) hℓ.le).2 (by dsimp [ℓ]; norm_num at hlog ⊢; exact hlog)
    exact_mod_cast hs.trans hJsqrt
  have hJpos : 0 < J := by omega
  have hJone : 1 ≤ J := by omega
  have hJfour : 4 ≤ J := by omega
  have hJ2 : ℓ ≤ (J : ℝ)^2 := by
    rw [← Real.sq_sqrt hℓ.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg ℓ) hJsqrt 2
  have hdJ : J ≤ d := hd
  have hfirst_nat : 100*J*J ≤ orbit ℓ d J := by
    calc
      100*J*J ≤ 100^J*d := Nat.mul_le_mul (hundred_mul_le_pow hJone) hdJ
      _ ≤ orbit ℓ d J := orbit_ge_geometric ℓ d J
  have hfirst : 100*ℓ ≤ (orbit ℓ d J : ℝ) := by
    have hcast : (100 : ℝ)*J*J ≤ orbit ℓ d J := by exact_mod_cast hfirst_nat
    nlinarith
  have hquadratic := quadratic_orbit_lower hℓ hfirst J
  have hpow : ℓ ≤ (↑(2^J : ℕ) : ℝ) :=
    hJ2.trans (by exact_mod_cast sq_le_two_pow hJfour)
  have hlog100 : (1 : ℝ) ≤ Real.log 100 :=
    (Real.le_log_iff_exp_le (by norm_num)).2 (by linarith [Real.exp_one_lt_three])
  have hexp : Real.exp ℓ ≤ (100 : ℝ)^(2^J) := by
    calc
      Real.exp ℓ ≤ Real.exp (((↑(2^J : ℕ) : ℝ)) * Real.log 100) :=
        Real.exp_le_exp.mpr (by nlinarith)
      _ = (100 : ℝ)^(2^J) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<100)]
  have hℓone : 1 ≤ ℓ := by dsimp [ℓ]; linarith
  have hreal : (n : ℝ) ≤ (orbit ℓ d (2*J) : ℝ) := by
    calc
      (n : ℝ) = Real.exp ℓ := (Real.exp_log (by exact_mod_cast hn)).symm
      _ ≤ (100 : ℝ)^(2^J) := hexp
      _ ≤ ℓ * (100 : ℝ)^(2^J) := le_mul_of_one_le_left (by positivity) hℓone
      _ ≤ (orbit ℓ (orbit ℓ d J) J : ℝ) := hquadratic
      _ = (orbit ℓ d (2*J) : ℝ) := by rw [← orbit_add]; congr 2; omega
  exact_mod_cast hreal

/-- Sufficient cost estimate for the unchanged subpower-loss tail. This does
not assert the sharper arbitrary-r logarithm-of-logarithm source estimate. -/
theorem cost_le_six_sqrt {n d : ℕ} (hn : 0 < n)
    (hlog : 256 ≤ Real.log (n : ℝ))
    (hd : ⌈Real.sqrt (Real.log (n : ℝ))⌉₊ ≤ d) :
    cost n (Real.log (n : ℝ)) d ≤ 6 * Real.sqrt (Real.log (n : ℝ)) := by
  let ℓ := Real.log (n : ℝ)
  let J : ℕ := ⌈Real.sqrt ℓ⌉₊
  have hℓ : 0 < ℓ := by dsimp [ℓ]; linarith
  have hspos : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ
  have hsone : 1 ≤ Real.sqrt ℓ :=
    (Real.le_sqrt (by norm_num) hℓ.le).2 (by dsimp [ℓ]; norm_num; linarith)
  have hJlow : Real.sqrt ℓ ≤ (J : ℝ) := Nat.le_ceil _
  have hJup : (J : ℝ) < Real.sqrt ℓ + 1 := Nat.ceil_lt_add_one (Real.sqrt_nonneg ℓ)
  have hdR : Real.sqrt ℓ ≤ (d : ℝ) := hJlow.trans (by exact_mod_cast hd)
  have hdposR : (0 : ℝ) < d := hspos.trans_le hdR
  have hdpos : 0 < d := by exact_mod_cast hdposR
  have hrecip : 2*ℓ/(d : ℝ) ≤ 2*Real.sqrt ℓ := by
    apply (div_le_iff₀ hdposR).2
    have hs := Real.sq_sqrt hℓ.le
    nlinarith
  have hcost := cost_le_count_and_reciprocal ℓ hℓ.le hdpos
    (orbit_reaches_dimension hn hlog hd)
  change cost n ℓ d ≤ 6*Real.sqrt ℓ
  have hcast : ((2*J : ℕ) : ℝ) = 2*(J : ℝ) := by norm_cast
  change cost n ℓ d ≤ ((2*J : ℕ) : ℝ) + 2*ℓ/d at hcost
  rw [hcast] at hcost
  linarith


/-- The deterministic singular-value threshold profile used in the source
induction. Its positivity and monotone ratio are genuine proved properties. -/
def profile (n : ℕ) (ℓ D : ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) / Real.sqrt (n : ℝ) * Real.exp (-D * cost n ℓ d)

theorem profile_pos {n d : ℕ} (hn : 0 < n) (hd : 0 < d) (ℓ D : ℝ) :
    0 < profile n ℓ D d := by
  unfold profile
  positivity

theorem profile_div_eq {n d : ℕ} (hd : 0 < d) (ℓ D : ℝ) :
    profile n ℓ D d / d =
      Real.exp (-D * cost n ℓ d) / Real.sqrt (n : ℝ) := by
  unfold profile
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

theorem profile_ratio_monotone {n d e : ℕ} {ℓ D : ℝ}
    (hℓ : 0 < ℓ) (hD : 0 ≤ D) (hd : 0 < d) (hde : d ≤ e) :
    profile n ℓ D d / d ≤ profile n ℓ D e / e := by
  rw [profile_div_eq hd, profile_div_eq (lt_of_lt_of_le hd hde)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply Real.exp_le_exp.mpr
  have := cost_antitone hℓ n hd hde
  nlinarith

theorem profile_recurrence {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (hdn : d < n) (ℓ D : ℝ) :
    profile n ℓ D d =
      ((d : ℝ) / (step ℓ d : ℝ)) *
      Real.exp (-D * (1 + ℓ / d)) * profile n ℓ D (step ℓ d) := by
  unfold profile
  rw [cost_recurrence ℓ hd hdn]
  have he : -D * (1 + ℓ / d + cost n ℓ (step ℓ d)) =
      -D * (1 + ℓ / d) + -D * cost n ℓ (step ℓ d) := by ring
  rw [he, Real.exp_add]
  have hs : (step ℓ d : ℝ) ≠ 0 := by exact_mod_cast (step_pos ℓ hd).ne'
  have hnR : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  field_simp


theorem step_cast_upper {ℓ : ℝ} (hℓ : 0 < ℓ) {d : ℕ} (hd : 0 < d) :
    (step ℓ d : ℝ) ≤ (d : ℝ)^2/ℓ + 100*d := by
  unfold step
  rw [Nat.cast_max, Nat.cast_mul]
  apply max_le
  · have := div_nonneg (sq_nonneg (d : ℝ)) hℓ.le
    norm_num
    linarith
  · have hc := Nat.ceil_lt_add_one (div_nonneg (sq_nonneg (d : ℝ)) hℓ.le)
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

theorem step_loss_le {ℓ : ℝ} (hℓ : 0 < ℓ) {d : ℕ} (hd : 0 < d) :
    1 + (step ℓ d : ℝ)*ℓ/(d : ℝ)^2 ≤ 2 + 100*ℓ/d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  calc
    1 + (step ℓ d : ℝ)*ℓ/(d : ℝ)^2 ≤
        1 + ((d : ℝ)^2/ℓ + 100*d)*ℓ/(d : ℝ)^2 := by
      gcongr
      exact step_cast_upper hℓ hd
    _ = 2 + 100*ℓ/d := by field_simp; ring

#assert_trust kernel step
#assert_trust kernel orbit
#assert_trust kernel cost
#assert_trust kernel step_ge_linear
#assert_trust kernel step_ge_self
#assert_trust kernel step_pos
#assert_trust kernel step_monotone
#assert_trust kernel step_ge_quadratic
#assert_trust kernel orbit_ge_start
#assert_trust kernel orbit_pos
#assert_trust kernel orbit_monotone_start
#assert_trust kernel orbit_monotone_index
#assert_trust kernel orbit_shift
#assert_trust kernel orbit_add
#assert_trust kernel orbit_ge_geometric
#assert_trust kernel orbit_ge_add
#assert_trust kernel orbit_terminated
#assert_trust kernel cost_zero_of_ge
#assert_trust kernel cost_antitone
#assert_trust kernel cost_recurrence
#assert_trust kernel reciprocal_sum_le
#assert_trust kernel hundred_mul_le_pow
#assert_trust kernel sq_le_two_pow
#assert_trust kernel quadratic_orbit_lower
#assert_trust kernel stopped_count_le
#assert_trust kernel cost_le_count_and_reciprocal
#assert_trust kernel orbit_reaches_dimension
#assert_trust kernel cost_le_six_sqrt
#assert_trust kernel profile
#assert_trust kernel profile_pos
#assert_trust kernel profile_div_eq
#assert_trust kernel profile_ratio_monotone
#assert_trust kernel profile_recurrence
#assert_trust kernel step_cast_upper
#assert_trust kernel step_loss_le
#print axioms step
#print axioms orbit
#print axioms cost
#print axioms step_ge_linear
#print axioms step_ge_self
#print axioms step_pos
#print axioms step_monotone
#print axioms step_ge_quadratic
#print axioms orbit_ge_start
#print axioms orbit_pos
#print axioms orbit_monotone_start
#print axioms orbit_monotone_index
#print axioms orbit_shift
#print axioms orbit_add
#print axioms orbit_ge_geometric
#print axioms orbit_ge_add
#print axioms orbit_terminated
#print axioms cost_zero_of_ge
#print axioms cost_antitone
#print axioms cost_recurrence
#print axioms reciprocal_sum_le
#print axioms hundred_mul_le_pow
#print axioms sq_le_two_pow
#print axioms quadratic_orbit_lower
#print axioms stopped_count_le
#print axioms cost_le_count_and_reciprocal
#print axioms orbit_reaches_dimension
#print axioms cost_le_six_sqrt
#print axioms profile
#print axioms profile_pos
#print axioms profile_div_eq
#print axioms profile_ratio_monotone
#print axioms profile_recurrence
#print axioms step_cast_upper
#print axioms step_loss_le

end NLA.IE06.ScalarRecurrence
