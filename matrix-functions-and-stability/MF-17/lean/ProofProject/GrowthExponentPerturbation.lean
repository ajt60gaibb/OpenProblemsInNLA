import ProofProject.GrowthRate

/-!
# Shrinking perturbations preserve the sharp exponent

The derivative of the exponent is bounded on every ray `[M,∞)` with `M>1`.
Consequently an error at most `1/n` changes `n^α` by one constant depending
only on `M`, without replacing the target exponent by a larger fixed one.
-/

noncomputable section

namespace ProofProject

lemma monotoneOn_growthExponent : MonotoneOn growthExponent (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact mul_le_mul_of_nonneg_left
    (Real.arccos_le_arccos (one_div_le_one_div_of_le hx hxy))
    (div_nonneg (by norm_num) Real.pi_pos.le)

def growthExponentSlope (x : ℝ) : ℝ :=
  (2 / Real.pi) * ((Real.sqrt (1 - x⁻¹ ^ 2))⁻¹ * (x ^ 2)⁻¹)

lemma hasDerivAt_growthExponent {x : ℝ} (hx : 1 < x) :
    HasDerivAt growthExponent (growthExponentSlope x) x := by
  have hx0 : 0 < x := by linarith
  have hi0 : 0 < x⁻¹ := inv_pos.mpr hx0
  have hi1 : x⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx
  have hd := ((Real.hasDerivAt_arccos (by linarith : x⁻¹ ≠ -1)
    (by linarith : x⁻¹ ≠ 1)).comp x (hasDerivAt_inv hx0.ne')).const_mul (2 / Real.pi)
  change HasDerivAt (fun y : ℝ => (2 / Real.pi) * Real.arccos (1 / y)) _ x
  simpa only [growthExponentSlope, one_div, neg_mul_neg, Function.comp_apply] using hd

/-- A derivative bound depending only on the fixed starting constant. -/
def growthExponentLipschitzConstant (M : ℝ) : ℝ :=
  (2 / Real.pi) * (Real.sqrt (1 - M⁻¹ ^ 2))⁻¹

lemma growthExponent_sqrt_pos {M : ℝ} (hM : 1 < M) :
    0 < Real.sqrt (1 - M⁻¹ ^ 2) := by
  have hi0 : 0 < M⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : M⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM
  apply Real.sqrt_pos.mpr
  nlinarith

lemma growthExponentLipschitzConstant_pos {M : ℝ} (hM : 1 < M) :
    0 < growthExponentLipschitzConstant M :=
  mul_pos (div_pos (by norm_num) Real.pi_pos)
    (inv_pos.mpr (growthExponent_sqrt_pos hM))

lemma growthExponentSlope_norm_le {M x : ℝ} (hM : 1 < M) (hx : M ≤ x) :
    ‖growthExponentSlope x‖ ≤ growthExponentLipschitzConstant M := by
  have hM0 : 0 < M := by linarith
  have hx0 : 0 < x := hM0.trans_le hx
  have hx1 : 1 < x := hM.trans_le hx
  have hi : x⁻¹ ≤ M⁻¹ := inv_anti₀ hM0 hx
  have hisq := pow_le_pow_left₀ (inv_nonneg.mpr hx0.le) hi 2
  have hsqrt : Real.sqrt (1 - M⁻¹ ^ 2) ≤ Real.sqrt (1 - x⁻¹ ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have hrootinv : (Real.sqrt (1 - x⁻¹ ^ 2))⁻¹ ≤ (Real.sqrt (1 - M⁻¹ ^ 2))⁻¹ :=
    inv_anti₀ (growthExponent_sqrt_pos hM) hsqrt
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  have hinv2 : (x ^ 2)⁻¹ ≤ 1 := by
    simpa only [inv_one] using inv_anti₀ (by norm_num : (0 : ℝ) < 1) hx2
  have hnonneg : 0 ≤ growthExponentSlope x := by
    unfold growthExponentSlope
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  unfold growthExponentSlope growthExponentLipschitzConstant
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (mul_le_of_le_one_right (by positivity) hinv2).trans hrootinv

/-- Increments of the exact exponent are uniformly linear on the entire ray. -/
theorem growthExponent_add_le {M ε : ℝ} (hM : 1 < M) (hε : 0 ≤ ε) :
    growthExponent (M + ε) ≤ growthExponent M + growthExponentLipschitzConstant M * ε := by
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (f := growthExponent) (f' := growthExponentSlope)
    (a := M) (b := M + ε) (C := growthExponentLipschitzConstant M)
    (fun x hx => (hasDerivAt_growthExponent (hM.trans_le hx.1)).hasDerivWithinAt)
    (fun x hx => growthExponentSlope_norm_le hM hx.1)
    (M + ε) (by constructor <;> linarith)
  have hle := (le_abs_self (growthExponent (M + ε) - growthExponent M)).trans
    (show |growthExponent (M + ε) - growthExponent M| ≤
      growthExponentLipschitzConstant M * ε by simpa only [Real.norm_eq_abs, add_sub_cancel_left] using hh)
  linarith

/-- A perturbation at most the reciprocal of the base changes its power by a
fixed factor. This holds for all real bases at least one. -/
theorem growthExponent_rpow_perturbation {M x ε : ℝ} (hM : 1 < M)
    (hx : 1 ≤ x) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / x) :
    x ^ growthExponent (M + ε) ≤
      Real.exp (growthExponentLipschitzConstant M) * x ^ growthExponent M := by
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hεlog : ε * Real.log x ≤ 1 := by
    calc
      _ ≤ (1 / x) * Real.log x := mul_le_mul_of_nonneg_right hε hlog0
      _ ≤ (1 / x) * x := mul_le_mul_of_nonneg_left (Real.log_le_self hx0.le)
        (one_div_pos.mpr hx0).le
      _ = 1 := one_div_mul_cancel hx0.ne'
  have hexp : Real.log x * growthExponent (M + ε) ≤
      growthExponentLipschitzConstant M + Real.log x * growthExponent M := by
    calc
      _ ≤ Real.log x * (growthExponent M + growthExponentLipschitzConstant M * ε) :=
        mul_le_mul_of_nonneg_left (growthExponent_add_le hM hε0) hlog0
      _ = Real.log x * growthExponent M + growthExponentLipschitzConstant M * (ε * Real.log x) := by ring
      _ ≤ Real.log x * growthExponent M + growthExponentLipschitzConstant M :=
        add_le_add le_rfl (mul_le_of_le_one_right (growthExponentLipschitzConstant_pos hM).le hεlog)
      _ = _ := add_comm _ _
  simpa only [Real.rpow_def_of_pos hx0, Real.exp_add] using Real.exp_le_exp.mpr hexp

/-- One constant works before both the integer dimension and its allowed
separation error are chosen. -/
theorem exists_growthExponent_perturbation_bound {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / (n : ℝ) →
      (n : ℝ) ^ growthExponent (M + ε) ≤ C * (n : ℝ) ^ growthExponent M := by
  refine ⟨Real.exp (growthExponentLipschitzConstant M), Real.exp_pos _, ?_⟩
  intro n hn ε hε0 hε
  exact growthExponent_rpow_perturbation hM (by exact_mod_cast hn) hε0 hε

/-- The source's choice `ε=1/n` retains exactly the exponent at `M`. -/
theorem exists_growthExponent_reciprocal_bound {M : ℝ} (hM : 1 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) ^ growthExponent (M + 1 / (n : ℝ)) ≤ C * (n : ℝ) ^ growthExponent M := by
  obtain ⟨C, hC, hb⟩ := exists_growthExponent_perturbation_bound hM
  exact ⟨C, hC, fun n hn => hb n hn _ (by positivity) le_rfl⟩

end ProofProject
