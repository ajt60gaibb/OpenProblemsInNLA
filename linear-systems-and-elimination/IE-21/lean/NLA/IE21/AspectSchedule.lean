import NLA.IE21.Definitions
import Mathlib.Tactic

/-! Exact all-aspect-ratio schedule for IE-21. No probabilistic theorem is assumed here.
Original analytic argument: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.IE21

lemma aspectParameter_tendsto_zero (m n : ℕ → ℕ)
    (hQ : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    Tendsto (fun j => aspectParameter (m j) (n j)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  simpa [aspectParameter] using
    (tendsto_const_nhds.mul (hlog.comp hQ).sqrt :
      Tendsto (fun j => (32 : ℝ) * Real.sqrt
        (Real.log ((m j : ℝ) / n j) / ((m j : ℝ) / n j))) atTop (𝓝 (32 * Real.sqrt 0)))

lemma aspectParameter_square (m n : ℕ) (hQ : 1 ≤ (m : ℝ) / n) :
    aspectParameter m n ^ 2 = 1024 * Real.log ((m : ℝ) / n) / ((m : ℝ) / n) := by
  have hpos : 0 < (m : ℝ) / n := lt_of_lt_of_le (by norm_num) hQ
  dsimp [aspectParameter]
  rw [mul_pow, Real.sq_sqrt (div_nonneg (Real.log_nonneg hQ) hpos.le)]
  ring

lemma power_exp_decay (b q c : ℝ) (n : ℕ) (hb : 0 ≤ b) (hbq : b ≤ q)
    (hq : 1 ≤ q) (hn : 1 ≤ n) (hc : 2 ≤ c) :
    b ^ n * Real.exp (-c * (n : ℝ) * Real.log q) ≤ Real.exp (-Real.log q) := by
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hl : 0 ≤ Real.log q := Real.log_nonneg hq
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnl : Real.log q ≤ (n : ℝ) * Real.log q := by nlinarith
  have hnln : 0 ≤ (n : ℝ) * Real.log q := mul_nonneg (Nat.cast_nonneg _) hl
  calc
    b ^ n * Real.exp (-c * (n : ℝ) * Real.log q) ≤
        q ^ n * Real.exp (-c * (n : ℝ) * Real.log q) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb hbq _) (Real.exp_pos _).le
    _ = Real.exp ((1 - c) * (n : ℝ) * Real.log q) := by
      rw [← Real.exp_log hqp, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      rw [Real.log_exp]
      ring
    _ ≤ Real.exp (-Real.log q) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) hnln]

lemma aspect_net_base_le (m n : ℕ) (hQ : 1 ≤ (m : ℝ) / n)
    (hlog : 1 ≤ Real.log ((m : ℝ) / n)) (hd : aspectParameter m n ≤ 1) :
    0 < aspectParameter m n ∧ 1 + 2 / aspectParameter m n ≤ (m : ℝ) / n := by
  let q : ℝ := (m : ℝ) / n
  let d : ℝ := aspectParameter m n
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hQ
  have hdp : 0 < d := by
    dsimp [d, aspectParameter]
    positivity
  have hs : d ^ 2 * q = 1024 * Real.log q := by
    have hd2 : d ^ 2 = 1024 * Real.log q / q := aspectParameter_square m n hQ
    rw [hd2, div_mul_cancel₀ _ hqp.ne']
  have hsq : (d * q) ^ 2 = 1024 * Real.log q * q := by nlinarith [congrArg (fun z : ℝ => z * q) hs]
  have hprod : 1 ≤ Real.log q * q := by
    change 1 ≤ q at hQ
    change 1 ≤ Real.log q at hlog
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hQ)]
  have hdq : 32 ≤ d * q := by nlinarith [mul_pos hdp hqp]
  refine ⟨hdp, ?_⟩
  have : 2 / d ≤ q - 1 := (div_le_iff₀ hdp).mpr (by dsimp [d] at *; nlinarith)
  dsimp [d, q] at *
  linarith

lemma finiteFailure_aspect_bound (m n : ℕ) (hn : 1 ≤ n)
    (hQ : 9 ≤ (m : ℝ) / n) (hlog : 1 ≤ Real.log ((m : ℝ) / n))
    (hd : aspectParameter m n ≤ 1) :
    finiteFailure m n (aspectParameter m n) (aspectParameter m n) (aspectParameter m n) ≤
      7 * Real.exp (-Real.log ((m : ℝ) / n)) := by
  let q : ℝ := (m : ℝ) / n
  let d : ℝ := aspectParameter m n
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 1) hn)
  have hq1 : 1 ≤ q := by dsimp [q]; linarith
  have hqp : 0 < q := lt_of_lt_of_le (by norm_num) hq1
  obtain ⟨hdp, hbase⟩ := aspect_net_base_le m n hq1 hlog hd
  have hmform : (m : ℝ) = q * n := by dsimp [q]; field_simp
  have hs : (m : ℝ) * d ^ 2 = 1024 * (n : ℝ) * Real.log q := by
    have hd2 : d ^ 2 = 1024 * Real.log q / q := aspectParameter_square m n hq1
    rw [hd2, hmform]
    field_simp [hqp.ne']
  have he1 : -(m : ℝ) * d ^ 2 / 512 = -2 * (n : ℝ) * Real.log q := by linarith
  have he2 : -2 * (m : ℝ) * d ^ 2 = -2048 * (n : ℝ) * Real.log q := by linarith
  have hfirst := power_exp_decay 9 q 2 n (by norm_num) hQ hq1 hn (by norm_num)
  have hsecond := power_exp_decay (1 + 2 / d) q 2048 n (by positivity) hbase hq1 hn (by norm_num)
  change 2 * 9 ^ n * Real.exp (-(m : ℝ) * d ^ 2 / 512) +
    5 * (1 + 2 / d) ^ n * Real.exp (-2 * (m : ℝ) * d ^ 2) ≤ 7 * Real.exp (-Real.log q)
  rw [he1, he2]
  nlinarith

lemma finiteFailure_nonneg (m n : ℕ) (t ε δ : ℝ) (hδ : 0 < δ) :
    0 ≤ finiteFailure m n t ε δ := by
  unfold finiteFailure
  positivity


theorem aspect_schedule (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n : ℕ → ℕ) (_hm : ∀ j, 1 ≤ m j) (hn : ∀ j, 1 ≤ n j)
    (hnlim : Tendsto n atTop atTop)
    (hQlim : Tendsto (fun j => (m j : ℝ) / n j) atTop atTop) :
    (∀ᶠ j in atTop, 2 ≤ n j ∧ 0 < aspectParameter (m j) (n j) ∧
      aspectParameter (m j) (n j) < 1 ∧
      aspectParameter (m j) (n j) ≤ (1 - θ) / 2) ∧
    Tendsto (fun j => finiteFailure (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) ∧
    Tendsto (fun j => finiteRatioError θ (m j) (n j)
      (aspectParameter (m j) (n j)) (aspectParameter (m j) (n j))
      (aspectParameter (m j) (n j))) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun j => aspectParameter (m j) (n j)
  let q : ℕ → ℝ := fun j => (m j : ℝ) / n j
  have hdlim : Tendsto d atTop (𝓝 0) := aspectParameter_tendsto_zero m n hQlim
  have hsmall : ∀ᶠ j in atTop, d j < 1 ∧ d j ≤ (1 - θ) / 2 := by
    filter_upwards [hdlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      hdlim.eventually (gt_mem_nhds (by linarith [hθ.2] : (0 : ℝ) < (1 - θ) / 2))]
      with j h1 h2 using ⟨h1, h2.le⟩
  have hadmissible : ∀ᶠ j in atTop, 2 ≤ n j ∧ 0 < d j ∧ d j < 1 ∧
      d j ≤ (1 - θ) / 2 := by
    filter_upwards [hnlim.eventually_ge_atTop 2, hQlim.eventually_gt_atTop 1, hsmall]
      with j hnj hqj hdj
    refine ⟨hnj, ?_, hdj⟩
    have hlog : 0 < Real.log ((m j : ℝ) / n j) := Real.log_pos hqj
    have hqp : 0 < (m j : ℝ) / n j := lt_trans (by norm_num) hqj
    dsimp [d, aspectParameter]
    positivity
  have hupper : ∀ᶠ j in atTop,
      finiteFailure (m j) (n j) (d j) (d j) (d j) ≤ 7 / q j := by
    filter_upwards [hQlim.eventually_ge_atTop 9,
      hQlim.eventually_ge_atTop (Real.exp 1), hsmall] with j hqj he hdj
    have hqp : 0 < (m j : ℝ) / n j := by linarith
    have hl : 1 ≤ Real.log ((m j : ℝ) / n j) := (Real.le_log_iff_exp_le hqp).mpr he
    have h := finiteFailure_aspect_bound (m j) (n j) (hn j) hqj hl hdj.1.le
    rw [Real.exp_neg, Real.exp_log hqp] at h
    simpa only [d, q, div_eq_mul_inv] using h
  have hfailure : Tendsto (fun j => finiteFailure (m j) (n j) (d j) (d j) (d j))
      atTop (𝓝 0) :=
    squeeze_zero' (hadmissible.mono (fun j hj => finiteFailure_nonneg _ _ _ _ _ hj.2.1))
      hupper (tendsto_const_nhds.div_atTop hQlim)
  have hnreal : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnlim
  have hmreal : Tendsto (fun j => (m j : ℝ)) atTop atTop := by
    have h := hQlim.atTop_mul_atTop₀ hnreal
    apply h.congr'
    filter_upwards [] with j
    exact div_mul_cancel₀ _ (by exact_mod_cast (Nat.ne_zero_of_lt (lt_of_lt_of_le (by omega : 0 < 1) (hn j))))
  have hrad : Tendsto (fun j => Real.sqrt (2 / (n j : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.div_atTop hnreal :
      Tendsto (fun j => (2 : ℝ) / n j) atTop (𝓝 0)).sqrt
  have hfirst : Tendsto (fun j => 2 * truncationScale θ * d j) atTop (𝓝 0) := by
    simpa using hdlim.const_mul (2 * truncationScale θ)
  have hsecond : Tendsto (fun j => truncationScale θ / (m j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hmreal
  have hthird : Tendsto (fun j => 2 * (1 + d j) * d j) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      hdlim).const_mul 2).mul hdlim
  have hD : Tendsto (fun j => trimmingError θ (m j) (d j) (d j) (d j)) atTop (𝓝 0) := by
    simpa [trimmingError] using (hfirst.add hsecond).add hthird
  have hden : Tendsto (fun j => 1 - d j) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hdlim
  have herror : Tendsto (fun j => finiteRatioError θ (m j) (n j) (d j) (d j) (d j))
      atTop (𝓝 0) := by
    have h := ((hD.add hrad).add hdlim).div hden (by norm_num)
    change Tendsto (fun j => (trimmingError θ (m j) (d j) (d j) (d j) +
      Real.sqrt (2 / (n j : ℝ)) + d j) / (1 - d j)) atTop (𝓝 ((0 + 0 + 0) / 1)) at h
    simpa only [finiteRatioError, zero_add, zero_div] using h
  exact ⟨hadmissible, hfailure, herror⟩

#print axioms aspect_schedule
end NLA.IE21
