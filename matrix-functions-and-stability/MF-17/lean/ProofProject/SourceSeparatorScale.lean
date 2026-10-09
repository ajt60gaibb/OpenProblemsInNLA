import ProofProject.SourcePieceScale

/-!
# The source separator rates and their finite geometric tails

All scale comparisons retain the exact doubly exponential source sequence.
The gap of two indices at a separator supplies its factor
`exp (-(log 16 / 18) * (4/3)^k)`. The remaining distances contribute ordinary
geometric factors, suitable for arbitrary finite sums.
-/

noncomputable section

namespace ProofProject

def sourceSeparatorRate (k : ℕ) : ℝ :=
  Real.sqrt (sourcePieceLambda (k + 1) * sourcePieceLambda (k + 2))

def sourceSeparatorDecay (k : ℕ) : ℝ :=
  Real.exp (-(Real.log 16 / 18) * (4 / 3 : ℝ) ^ k)

theorem sourceSeparatorRate_pos (k : ℕ) : 0 < sourceSeparatorRate k :=
  Real.sqrt_pos.2 (mul_pos (sourcePieceLambda_pos _) (sourcePieceLambda_pos _))

theorem sourceSeparatorDecay_pos (k : ℕ) : 0 < sourceSeparatorDecay k :=
  Real.exp_pos _

theorem sourceSeparatorRate_nonneg (k : ℕ) : 0 ≤ sourceSeparatorRate k :=
  (sourceSeparatorRate_pos k).le

theorem sourceSeparatorDecay_nonneg (k : ℕ) : 0 ≤ sourceSeparatorDecay k :=
  (sourceSeparatorDecay_pos k).le

theorem sourceSeparatorDecay_le_one (k : ℕ) : sourceSeparatorDecay k ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have hL : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (div_nonneg hL (by norm_num)))
    (by positivity)

theorem sourceSeparatorDecay_antitone : Antitone sourceSeparatorDecay := by
  intro k l hkl
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log 16 / 18 :=
    div_nonneg (Real.log_nonneg (by norm_num)) (by norm_num)
  exact mul_le_mul_of_nonpos_left
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4 / 3) hkl) (neg_nonpos.mpr hL)

theorem sourcePieceLambda_eq_exp (q : ℕ) :
    sourcePieceLambda q = Real.exp (-(Real.log 16 / 2) * (4 / 3 : ℝ) ^ q) := by
  rw [sourcePieceLambda, Real.rpow_def_of_pos (sourcePieceScale_pos q), log_sourcePieceScale]
  congr 1
  ring

theorem sourceSeparatorRate_eq_exp (k : ℕ) :
    sourceSeparatorRate k = Real.exp (-(7 * Real.log 16 / 9) * (4 / 3 : ℝ) ^ k) := by
  rw [sourceSeparatorRate, sourcePieceLambda_eq_exp, sourcePieceLambda_eq_exp,
    ← Real.exp_add, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  congr 1
  simp only [pow_succ]
  ring

/-- A coarse logarithm bound is enough for both numerical geometric ratios. -/
theorem two_le_log_sixteen : (2 : ℝ) ≤ Real.log 16 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)
  rw [Real.log_inv] at h
  have hpow := Real.log_pow (2 : ℝ) 4
  norm_num at hpow
  rw [hpow]
  norm_num at h
  linarith

/-- Successive increments of `(4/3)^q` are at least `1/3`. -/
theorem sourceScaleExponent_gap {p q : ℕ} (hpq : p ≤ q) :
    ((q - p : ℕ) : ℝ) / 3 ≤ (4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  clear hpq
  simp only [Nat.add_sub_cancel_left]
  induction d with
  | zero => simp
  | succ d ih =>
      have hpow : (1 : ℝ) ≤ (4 / 3 : ℝ) ^ (p + d) := one_le_pow₀ (by norm_num)
      simp only [Nat.add_succ, Nat.add_zero, pow_succ, Nat.cast_succ]
      nlinarith

private theorem exp_neg_sixth_le : Real.exp (-1 / 6 : ℝ) ≤ 7 / 8 := by
  rw [show (-1 / 6 : ℝ) = -(1 / 6) by ring, Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.add_one_le_exp (1 / 6 : ℝ)
  nlinarith

private theorem exp_neg_twelfth_le : Real.exp (-1 / 12 : ℝ) ≤ 15 / 16 := by
  rw [show (-1 / 12 : ℝ) = -(1 / 12) by ring, Real.exp_neg]
  rw [← one_div]
  apply (div_le_iff₀ (Real.exp_pos _)).mpr
  have h := Real.add_one_le_exp (1 / 12 : ℝ)
  nlinarith

private theorem sourceScale_exp_gap_le {p q : ℕ} (hpq : p ≤ q)
    {β ρ : ℝ} (hβ : 0 ≤ β) (hρ : Real.exp (-(Real.log 16 * β / 3)) ≤ ρ) :
    Real.exp (-(Real.log 16 * β) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ p)) ≤
      ρ ^ (q - p) := by
  have hL : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.exp (((q - p : ℕ) : ℝ) * (-(Real.log 16 * β / 3))) := by
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (sourceScaleExponent_gap hpq) (mul_nonneg hL hβ)
      nlinarith
    _ = Real.exp (-(Real.log 16 * β / 3)) ^ (q - p) := Real.exp_nat_mul _ _
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hρ _

private theorem sourceScale_exp_quarter_gap_le {p q : ℕ} (hpq : p ≤ q) :
    Real.exp (-(Real.log 16 / 4) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ p)) ≤
      (7 / 8 : ℝ) ^ (q - p) := by
  have hρ : Real.exp (-(Real.log 16 * (1 / 4) / 3)) ≤ 7 / 8 := by
    apply le_trans (Real.exp_le_exp.mpr ?_) exp_neg_sixth_le
    have h := two_le_log_sixteen
    linarith
  simpa only [mul_one_div] using sourceScale_exp_gap_le hpq (by norm_num : (0 : ℝ) ≤ 1 / 4) hρ

private theorem sourceScale_exp_third_gap_le {p q : ℕ} (hpq : p ≤ q) :
    Real.exp (-(Real.log 16 / 3) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ p)) ≤
      (7 / 8 : ℝ) ^ (q - p) := by
  have hρ : Real.exp (-(Real.log 16 * (1 / 3) / 3)) ≤ 7 / 8 := by
    apply le_trans (Real.exp_le_exp.mpr ?_) exp_neg_sixth_le
    have h := two_le_log_sixteen
    linarith
  simpa only [mul_one_div] using sourceScale_exp_gap_le hpq (by norm_num : (0 : ℝ) ≤ 1 / 3) hρ

private theorem sourceScale_exp_eighth_gap_le {p q : ℕ} (hpq : p ≤ q) :
    Real.exp (-(Real.log 16 / 8) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ p)) ≤
      (15 / 16 : ℝ) ^ (q - p) := by
  have hρ : Real.exp (-(Real.log 16 * (1 / 8) / 3)) ≤ 15 / 16 := by
    apply le_trans (Real.exp_le_exp.mpr ?_) exp_neg_twelfth_le
    have h := two_le_log_sixteen
    linarith
  simpa only [mul_one_div] using sourceScale_exp_gap_le hpq (by norm_num : (0 : ℝ) ≤ 1 / 8) hρ

/-- The deleted side of a separator. -/
theorem sourceSeparatorRate_deleted_le {q k : ℕ} (hqk : q ≤ k) :
    Real.sqrt (sourceSeparatorRate k / sourcePieceLambda (q + 1)) ≤
      sourceSeparatorDecay k * (7 / 8 : ℝ) ^ (k - q) := by
  have heq : Real.sqrt (sourceSeparatorRate k / sourcePieceLambda (q + 1)) =
      sourceSeparatorDecay k *
        Real.exp (-(Real.log 16 / 3) * ((4 / 3 : ℝ) ^ k - (4 / 3 : ℝ) ^ q)) := by
    rw [sourceSeparatorRate_eq_exp, sourcePieceLambda_eq_exp, ← Real.exp_sub,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      sourceSeparatorDecay, ← Real.exp_add]
    congr 1
    rw [pow_succ]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (sourceScale_exp_third_gap_le hqk)
    (sourceSeparatorDecay_pos k).le

/-- The retained side of a separator, after the two-index gap. -/
theorem sourceSeparatorRate_retained_le {q k : ℕ} (hkq : k + 2 ≤ q) :
    Real.sqrt (sourcePieceLambda q / sourceSeparatorRate k) ≤
      sourceSeparatorDecay k * (7 / 8 : ℝ) ^ (q - (k + 2)) := by
  have heq : Real.sqrt (sourcePieceLambda q / sourceSeparatorRate k) =
      sourceSeparatorDecay k *
        Real.exp (-(Real.log 16 / 4) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ (k + 2))) := by
    rw [sourceSeparatorRate_eq_exp, sourcePieceLambda_eq_exp, ← Real.exp_sub,
      Real.sqrt_eq_rpow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      sourceSeparatorDecay, ← Real.exp_add]
    congr 1
    simp only [pow_succ]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (sourceScale_exp_quarter_gap_le hkq)
    (sourceSeparatorDecay_pos k).le

theorem sourcePieceScale_neg_eighth_eq_exp (q : ℕ) :
    sourcePieceScale q ^ (-1 / 8 : ℝ) =
      Real.exp (-(Real.log 16 / 8) * (4 / 3 : ℝ) ^ q) := by
  rw [Real.rpow_def_of_pos (sourcePieceScale_pos q), log_sourcePieceScale]
  congr 1
  ring

theorem sqrt_sourcePieceScale_neg_quarter (q : ℕ) :
    Real.sqrt (sourcePieceScale q ^ (-1 / 4 : ℝ)) = sourcePieceScale q ^ (-1 / 8 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (sourcePieceScale_pos q).le]
  norm_num

/-- The summable remainder scale. -/
theorem sourcePieceScale_sqrt_remainder_le {J q : ℕ} (hJq : J ≤ q) :
    Real.sqrt (sourcePieceScale q ^ (-1 / 4 : ℝ)) ≤
      (15 / 16 : ℝ) ^ (q - J) * sourcePieceScale J ^ (-1 / 8 : ℝ) := by
  rw [sqrt_sourcePieceScale_neg_quarter, sourcePieceScale_neg_eighth_eq_exp,
    sourcePieceScale_neg_eighth_eq_exp]
  have heq : Real.exp (-(Real.log 16 / 8) * (4 / 3 : ℝ) ^ q) =
      Real.exp (-(Real.log 16 / 8) * ((4 / 3 : ℝ) ^ q - (4 / 3 : ℝ) ^ J)) *
        Real.exp (-(Real.log 16 / 8) * (4 / 3 : ℝ) ^ J) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_right (sourceScale_exp_eighth_gap_le hJq) (Real.exp_pos _).le

theorem sourcePieceScale_neg_eighth_le_separatorDecay (J : ℕ) :
    sourcePieceScale J ^ (-1 / 8 : ℝ) ≤ sourceSeparatorDecay J := by
  rw [sourcePieceScale_neg_eighth_eq_exp, sourceSeparatorDecay]
  apply Real.exp_le_exp.mpr
  have hL : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  have hp : 0 ≤ (4 / 3 : ℝ) ^ J := by positivity
  nlinarith [mul_nonneg hL hp]

theorem sourcePieceScale_neg_eighth_geometric_le {J q : ℕ} (hJq : J ≤ q) :
    sourcePieceScale q ^ (-1 / 8 : ℝ) ≤
      (15 / 16 : ℝ) ^ (q - J) * sourcePieceScale J ^ (-1 / 8 : ℝ) := by
  simpa only [sqrt_sourcePieceScale_neg_quarter] using sourcePieceScale_sqrt_remainder_le hJq

end ProofProject
