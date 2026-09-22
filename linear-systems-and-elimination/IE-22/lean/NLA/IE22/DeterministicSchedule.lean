import NLA.IE22.Definitions

/-! Exact source schedule and quantitative deterministic error bounds.
Original mathematical proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
namespace NLA.IE22
open NLA.IE21

lemma errorSchedule_tendsto_zero : Tendsto errorSchedule atTop (𝓝 0) := by
  exact (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
    tendsto_natCast_atTop_atTop

lemma schedule_power_identities (n : ℕ) (hn : 1 ≤ n) :
    0 < errorSchedule n ∧
    (n : ℝ) * errorSchedule n ^ 6 = 1 ∧
    Real.rpow (n : ℝ) (2 / 3 : ℝ) * errorSchedule n ^ 4 = 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hp (k : ℕ) : errorSchedule n ^ k = Real.rpow (n : ℝ) (-(1/6 : ℝ) * k) := by
    change ((n : ℝ) ^ (-(1/6 : ℝ))) ^ k = (n : ℝ) ^ (-(1/6 : ℝ) * k)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le]
  refine ⟨Real.rpow_pos_of_pos hnpos _, ?_, ?_⟩
  · rw [hp]
    change (n : ℝ) * (n : ℝ) ^ (-(1/6 : ℝ) * 6) = 1
    conv_lhs => lhs; rw [← Real.rpow_one (n : ℝ)]
    rw [← Real.rpow_add hnpos]
    norm_num
  · rw [hp]
    change (n : ℝ) ^ (2/3 : ℝ) * (n : ℝ) ^ (-(1/6 : ℝ) * 4) = 1
    rw [← Real.rpow_add hnpos]
    norm_num

lemma schedule_dimension_bounds (n : ℕ) (hn : 1 ≤ n)
    (hd : errorSchedule n ≤ 1/2) :
    1 ≤ deletionSchedule n ∧ deletionSchedule n < n ∧
    (deletionSchedule n : ℝ) ≤ (n : ℝ) * errorSchedule n ^ 2 ∧
    1 / ((deletionSchedule n : ℝ) + 1) ≤ errorSchedule n ^ 4 ∧
    (n : ℝ) / 2 ≤ ((n - deletionSchedule n : ℕ) : ℝ) := by
  let d := errorSchedule n
  let s := Real.rpow (n : ℝ) (2/3 : ℝ)
  obtain ⟨hdpos, hn6, hs4⟩ := schedule_power_identities n hn
  change 0 < d at hdpos
  change (n : ℝ) * d^6 = 1 at hn6
  change s * d^4 = 1 at hs4
  change d ≤ 1/2 at hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs0 : 0 ≤ s := Real.rpow_nonneg hnpos.le _
  have hd2 : d^2 ≤ 1/2 := by nlinarith
  have hd4 : d^4 ≤ 1 := by nlinarith [sq_nonneg (d^2)]
  have hs1 : 1 ≤ s := by nlinarith [mul_le_mul_of_nonneg_left hd4 hs0]
  have heq : s = (n : ℝ) * d^2 := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hdpos.ne')
    calc
      s * d^4 = 1 := hs4
      _ = ((n : ℝ) * d^2) * d^4 := by nlinarith [hn6]
  have hr1 : 1 ≤ deletionSchedule n := by
    change 1 ≤ ⌊s⌋₊
    exact Nat.le_floor (by simpa only [Nat.cast_one] using hs1)
  have hr : (deletionSchedule n : ℝ) ≤ s := Nat.floor_le hs0
  have hrhalf : (deletionSchedule n : ℝ) ≤ (n : ℝ) / 2 := by
    rw [heq] at hr
    nlinarith [mul_le_mul_of_nonneg_left hd2 hnpos.le]
  have hrn : deletionSchedule n < n := by
    exact_mod_cast (show (deletionSchedule n : ℝ) < n by linarith)
  refine ⟨hr1, hrn, heq ▸ hr, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : (0 : ℝ) < deletionSchedule n + 1)).2
    have hslt : s < (deletionSchedule n : ℝ) + 1 := Nat.lt_floor_add_one s
    nlinarith [mul_le_mul_of_nonneg_right hslt.le (pow_nonneg hdpos.le 4)]
  · rw [Nat.cast_sub hrn.le]
    linarith

lemma schedule_failure_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (hd : errorSchedule n ≤ 1/2) :
    deterministicFailure θ n (deletionSchedule n) (errorSchedule n) ≤
      (6 + 4 * truncationScale θ ^ 2 + 8 * truncationScale θ) * errorSchedule n := by
  let d := errorSchedule n
  let r := deletionSchedule n
  let L := truncationScale θ
  obtain ⟨hdpos, hn6, _⟩ := schedule_power_identities n hn
  obtain ⟨_, hrn, _, hrinv, hdim⟩ := schedule_dimension_bounds n hn hd
  change 0 < d at hdpos
  change d ≤ 1/2 at hd
  change (n : ℝ) * d^6 = 1 at hn6
  change 1 / ((r : ℝ) + 1) ≤ d^4 at hrinv
  have hgap : 0 < 1 - θ := sub_pos.mpr hθ.2
  have hL : 0 ≤ L := by dsimp [L, truncationScale]; positivity
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdimpos : (0 : ℝ) < (n-r : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hrn)
  have hdinv : 1 / ((n-r : ℕ) : ℝ) ≤ 2 * d^6 := by
    have hninv : 1 / (n : ℝ) = d^6 := (div_eq_iff hnpos.ne').2 (by nlinarith [hn6])
    calc
      1 / ((n-r : ℕ) : ℝ) ≤ 1 / ((n : ℝ)/2) :=
        one_div_le_one_div_of_le (by positivity) hdim
      _ = 2 * (1 / (n : ℝ)) := by ring
      _ = 2 * d^6 := by rw [hninv]
  have hfirst : 2 / ((r : ℝ)+1) ≤ 2 * d^4 := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrinv (by norm_num : (0 : ℝ) ≤ 2)
  have hsecond : 4*L*(L/d+2) / (((r : ℝ)+1)*d^2) ≤
      4*L*(L+2*d)*d := by
    have hmult := mul_le_mul_of_nonneg_left hrinv
      (show 0 ≤ 4*L*(L/d+2)/d^2 by positivity)
    calc
      _ = (4*L*(L/d+2)/d^2)*(1/((r : ℝ)+1)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (4*L*(L/d+2)/d^2)*d^4 := hmult
      _ = _ := by field_simp [hdpos.ne']
  have hthird : 2 / (((n-r : ℕ) : ℝ)*d^2) ≤ 4*d^4 := by
    have hmult := mul_le_mul_of_nonneg_left hdinv (show 0 ≤ 2/d^2 by positivity)
    calc
      _ = (2/d^2)*(1/((n-r : ℕ) : ℝ)) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ (2/d^2)*(2*d^6) := hmult
      _ = _ := by field_simp [hdpos.ne']; ring
  have hd2 : d^2 ≤ d := by nlinarith
  have hd4 : d^4 ≤ d := by
    have hsq : d^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd2 hdpos.le]
  have hL2 : 0 ≤ L^2 := sq_nonneg L
  change 2 / ((r : ℝ)+1) + 4*L*(L/d+2) / (((r : ℝ)+1)*d^2) +
    2 / (((n-r : ℕ) : ℝ)*d^2) ≤ (6+4*L^2+8*L)*d
  nlinarith [mul_le_mul_of_nonneg_left hd2 hL]

lemma schedule_deterministic_bound (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (n : ℕ) (hn : 1 ≤ n) (hd : errorSchedule n ≤ 1/2) :
    deterministicBound θ n (deletionSchedule n) (errorSchedule n) - gaussianTrim θ ≤
      16 * errorSchedule n := by
  let d := errorSchedule n
  let r := deletionSchedule n
  let h := gaussianTrim θ
  obtain ⟨hdpos, _, _⟩ := schedule_power_identities n hn
  obtain ⟨_, hrn, hrbound, _, _⟩ := schedule_dimension_bounds n hn hd
  change 0 < d at hdpos
  change d ≤ 1/2 at hd
  change (r : ℝ) ≤ (n : ℝ)*d^2 at hrbound
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdimpos : (0 : ℝ) < (n-r : ℕ) := by exact_mod_cast (Nat.sub_pos_of_lt hrn)
  have hgap : 0 < 1-d := by linarith
  have h0 : 0 ≤ h := (gaussian_constant θ hθ).2.2.2.2.1
  have h1 : h ≤ 1 := (gaussian_constant θ hθ).2.2.2.2.2
  have hdim : (n : ℝ)*(1-d) ≤ ((n-r : ℕ) : ℝ) := by
    rw [Nat.cast_sub hrn.le]
    have hd2 : d^2 ≤ d := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hd2 hnpos.le]
  have hratio : (n : ℝ) / (((n-r : ℕ) : ℝ)*(1-d)) ≤ 1/(1-d)^2 := by
    apply (div_le_div_iff₀ (mul_pos hdimpos hgap) (sq_pos_of_pos hgap)).2
    nlinarith [mul_le_mul_of_nonneg_right hdim hgap.le]
  have hden : 1/4 ≤ (1-d)^2 := by nlinarith
  have hupper : (h+2*d)/(1-d)^2 ≤ h+16*d := by
    apply (div_le_iff₀ (sq_pos_of_pos hgap)).2
    have hnum : h+2*d-h*(1-d)^2 ≤ 4*d := by
      nlinarith [mul_nonneg h0 (sq_nonneg d), mul_le_mul_of_nonneg_right h1 hdpos.le]
    have hscale := mul_le_mul_of_nonneg_left hden (show 0 ≤ 16*d by positivity)
    nlinarith
  have hB := mul_le_mul_of_nonneg_right hratio (show 0 ≤ h+2*d by positivity)
  change (n : ℝ) / (((n-r : ℕ) : ℝ)*(1-d)) * (h+2*d) - h ≤ 16*d
  have hform : (1/(1-d)^2)*(h+2*d) = (h+2*d)/(1-d)^2 := by ring
  rw [hform] at hB
  linarith

theorem deterministic_schedule (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (∀ᶠ n in atTop, 1 ≤ deletionSchedule n ∧ deletionSchedule n < n ∧
      0 < errorSchedule n ∧ errorSchedule n < 1 ∧
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) < 1) ∧
    Tendsto errorSchedule atTop (𝓝 0) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) ≤ C * errorSchedule n ∧
      deterministicBound θ n (deletionSchedule n) (errorSchedule n) - gaussianTrim θ ≤
        C * errorSchedule n := by
  let L := truncationScale θ
  let C := 22 + 4*L^2 + 8*L
  have hgap : 0 < 1-θ := sub_pos.mpr hθ.2
  have hL : 0 ≤ L := by dsimp [L,truncationScale]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hsmall : ∀ᶠ n : ℕ in atTop, 1 ≤ n ∧ errorSchedule n ≤ 1/2 := by
    filter_upwards [eventually_ge_atTop 1,
      errorSchedule_tendsto_zero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))]
      with n hn hd using ⟨hn,hd.le⟩
  have hbounds : ∀ᶠ n in atTop,
      deterministicFailure θ n (deletionSchedule n) (errorSchedule n) ≤ C*errorSchedule n ∧
      deterministicBound θ n (deletionSchedule n) (errorSchedule n)-gaussianTrim θ ≤
        C*errorSchedule n := by
    filter_upwards [hsmall] with n hn
    have hd := (schedule_power_identities n hn.1).1
    have hf := schedule_failure_bound θ hθ n hn.1 hn.2
    have hb := schedule_deterministic_bound θ hθ n hn.1 hn.2
    change _ ≤ (6+4*L^2+8*L)*errorSchedule n at hf
    dsimp [C]
    constructor
    · nlinarith
    · nlinarith [mul_nonneg (sq_nonneg L) hd.le, mul_nonneg hL hd.le]
  have hCzero : Tendsto (fun n => C*errorSchedule n) atTop (𝓝 0) := by
    simpa using errorSchedule_tendsto_zero.const_mul C
  refine ⟨?_, errorSchedule_tendsto_zero, C, hC, hbounds⟩
  filter_upwards [hsmall, hbounds,
    hCzero.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with n hn hb hf
  obtain ⟨hr1,hrn,_,_,_⟩ := schedule_dimension_bounds n hn.1 hn.2
  exact ⟨hr1,hrn,(schedule_power_identities n hn.1).1,by linarith [hn.2],hb.1.trans_lt hf⟩

end NLA.IE22
