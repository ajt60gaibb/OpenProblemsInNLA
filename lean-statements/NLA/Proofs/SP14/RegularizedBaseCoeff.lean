import NLA.Proofs.SP14.BaseCoeffSummable
import Mathlib.Analysis.PSeries

/-!
The endpoint-cancelled coefficients of `(1+s)g₀(s)`. The eventual
weighted summability at exponent `9/8` is a genuine Wiener prerequisite;
Fourier identification and background product bounds are separate modules.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- Coefficient at `s⁻ⁿ` after multiplying the normalized exterior factor
by `1+s`. The additional coefficient at `s¹` is `1`. -/
noncomputable def regularizedBaseCoeff (n : ℕ) : ℂ :=
  baseCoeff n + baseCoeff (n + 1)

private theorem baseCoeff_succ_mul_public (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * baseCoeff (n + 1) =
      ((1 / 2 : ℂ) - n) * baseCoeff n := by
  unfold baseCoeff
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul]
  simp only [smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  rw [descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub]
  simp only [Polynomial.smeval_X, Polynomial.smeval_natCast, pow_zero,
    mul_one, nsmul_eq_mul]
  have hf : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  field_simp [hf, hn]

theorem regularizedBaseCoeff_recurrence (n : ℕ) :
    ((n + 1 : ℕ) : ℂ) * regularizedBaseCoeff n =
      (3 / 2 : ℂ) * baseCoeff n := by
  rw [regularizedBaseCoeff]
  have h := baseCoeff_succ_mul_public n
  push_cast at h ⊢
  linear_combination h

theorem regularizedBaseCoeff_zero : regularizedBaseCoeff 0 = 3 / 2 := by
  norm_num [regularizedBaseCoeff, baseCoeff, Ring.choose_one_right]

theorem regularizedBaseCoeff_one : regularizedBaseCoeff 1 = 3 / 8 := by
  have hc1 : baseCoeff 1 = (1 / 2 : ℂ) := by
    norm_num [baseCoeff, Ring.choose_one_right]
  have hc2 : baseCoeff 2 = (-1 / 8 : ℂ) := by
    have h := baseCoeff_succ_mul_public 1
    rw [hc1] at h
    norm_num at h
    linear_combination h / 2
  norm_num [regularizedBaseCoeff, hc1, hc2]

theorem regularizedBaseCoeff_two : regularizedBaseCoeff 2 = -1 / 16 := by
  have hc1 : baseCoeff 1 = (1 / 2 : ℂ) := by
    norm_num [baseCoeff, Ring.choose_one_right]
  have hc2 : baseCoeff 2 = (-1 / 8 : ℂ) := by
    have h := baseCoeff_succ_mul_public 1
    rw [hc1] at h
    norm_num at h
    linear_combination h / 2
  have hc3 : baseCoeff 3 = (1 / 16 : ℂ) := by
    have h := baseCoeff_succ_mul_public 2
    rw [hc2] at h
    norm_num at h
    linear_combination h / 3
  norm_num [regularizedBaseCoeff, hc2, hc3]

private theorem baseCoeff_norm_succ_public (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) + 1) * ‖baseCoeff (n + 1)‖ =
      ((n : ℝ) - 1 / 2) * ‖baseCoeff n‖ := by
  have hnonpos : (1 / 2 : ℝ) - n ≤ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hfactor : ‖(1 / 2 : ℂ) - (n : ℂ)‖ = (n : ℝ) - 1 / 2 := by
    have hcast : (1 / 2 : ℂ) - (n : ℂ) = (((1 / 2 : ℝ) - n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hnonpos]
    ring
  have h := congrArg norm (baseCoeff_succ_mul_public n)
  have hnat : ‖((n + 1 : ℕ) : ℂ)‖ = (n : ℝ) + 1 := by
    rw [Complex.norm_natCast]
    push_cast
    ring
  rw [norm_mul, norm_mul, hnat, hfactor] at h
  exact h

private theorem baseCoeff_norm_cubic_bound (n : ℕ) :
    ((n : ℝ) + 1) ^ 3 * ‖baseCoeff n‖ ^ 2 ≤ 2 := by
  have hmono (k : ℕ) (hk : 1 ≤ k) :
      ((k : ℝ) + 2) ^ 3 * ‖baseCoeff (k + 1)‖ ^ 2 ≤
        ((k : ℝ) + 1) ^ 3 * ‖baseCoeff k‖ ^ 2 := by
    let x : ℝ := k
    let A : ℝ := ‖baseCoeff k‖
    let B : ℝ := ‖baseCoeff (k + 1)‖
    have hx : 1 ≤ x := by
      change (1 : ℝ) ≤ (k : ℝ)
      exact_mod_cast hk
    have hx1 : 0 < x + 1 := by linarith
    have hr : (x + 1) * B = (x - 1 / 2) * A :=
      baseCoeff_norm_succ_public k hk
    have hB : B = ((x - 1 / 2) / (x + 1)) * A := by
      field_simp
      nlinarith [hr]
    have hpoly : (x + 2) ^ 3 * (x - 1 / 2) ^ 2 ≤ (x + 1) ^ 5 := by
      have hxsq : 0 ≤ x ^ 2 := by positivity
      have hxcube : 0 ≤ x ^ 3 := by positivity
      nlinarith
    have hratio :
        ((x + 2) ^ 3 * (x - 1 / 2) ^ 2) / (x + 1) ^ 2 ≤
          (x + 1) ^ 3 := by
      apply (div_le_iff₀ (pow_pos hx1 2)).mpr
      nlinarith [hpoly]
    change (x + 2) ^ 3 * B ^ 2 ≤ (x + 1) ^ 3 * A ^ 2
    rw [hB]
    calc
      (x + 2) ^ 3 * (((x - 1 / 2) / (x + 1)) * A) ^ 2 =
          (((x + 2) ^ 3 * (x - 1 / 2) ^ 2) / (x + 1) ^ 2) * A ^ 2 := by
            field_simp
      _ ≤ (x + 1) ^ 3 * A ^ 2 :=
        mul_le_mul_of_nonneg_right hratio (sq_nonneg A)
  cases n with
  | zero => norm_num [baseCoeff]
  | succ n =>
      induction n with
      | zero => norm_num [baseCoeff, Ring.choose_one_right]
      | succ n ih =>
          have hm := hmono (n + 1) (by omega)
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hm.trans ih

private theorem regularizedBaseCoeff_norm_recurrence (n : ℕ) :
    ((n : ℝ) + 1) * ‖regularizedBaseCoeff n‖ =
      (3 / 2 : ℝ) * ‖baseCoeff n‖ := by
  have h := congrArg norm (regularizedBaseCoeff_recurrence n)
  rw [norm_mul, norm_mul, Complex.norm_natCast] at h
  norm_num at h
  exact h

private theorem baseCoeff_norm_rpow_bound (n : ℕ) :
    (((n : ℝ) + 1) ^ (3 / 2 : ℝ)) * ‖baseCoeff n‖ ≤ 2 := by
  let x : ℝ := (n : ℝ) + 1
  let a : ℝ := ‖baseCoeff n‖
  have hx : 0 < x := by dsimp [x]; positivity
  have ha : 0 ≤ a := norm_nonneg _
  have hpower : (x ^ (3 / 2 : ℝ)) ^ 2 = x ^ 3 := by
    rw [← Real.rpow_mul_natCast (le_of_lt hx)]
    norm_num
  have hcubic : x ^ 3 * a ^ 2 ≤ 2 := baseCoeff_norm_cubic_bound n
  change x ^ (3 / 2 : ℝ) * a ≤ 2
  have hnonneg : 0 ≤ x ^ (3 / 2 : ℝ) * a :=
    mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) ha
  nlinarith [hpower, hcubic]

private theorem regularizedBaseCoeff_weighted_le (n : ℕ) :
    (((n : ℝ) + 1) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖ ≤
      3 / (((n : ℝ) + 1) ^ (11 / 8 : ℝ)) := by
  let x : ℝ := (n : ℝ) + 1
  let a : ℝ := ‖baseCoeff n‖
  let d : ℝ := ‖regularizedBaseCoeff n‖
  have hx : 0 < x := by dsimp [x]; positivity
  have hr : x * d = (3 / 2 : ℝ) * a := regularizedBaseCoeff_norm_recurrence n
  have hbound : x ^ (3 / 2 : ℝ) * a ≤ 2 := baseCoeff_norm_rpow_bound n
  change x ^ (9 / 8 : ℝ) * d ≤ 3 / x ^ (11 / 8 : ℝ)
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hx _)).mpr
  calc
    x ^ (9 / 8 : ℝ) * d * x ^ (11 / 8 : ℝ) =
        (x ^ (9 / 8 : ℝ) * x ^ (11 / 8 : ℝ)) * d := by ring
    _ = x ^ (5 / 2 : ℝ) * d := by
      rw [← Real.rpow_add hx]
      norm_num
    _ = x ^ (3 / 2 : ℝ) * (x * d) := by
      have he : (5 / 2 : ℝ) = 3 / 2 + 1 := by norm_num
      rw [he, Real.rpow_add hx]
      simp
      ring
    _ = (3 / 2 : ℝ) * (x ^ (3 / 2 : ℝ) * a) := by rw [hr]; ring
    _ ≤ 3 := by nlinarith

theorem summable_regularizedBaseCoeff_weighted :
    Summable (fun n : ℕ =>
      (((n : ℝ) + 1) ^ (9 / 8 : ℝ)) * ‖regularizedBaseCoeff n‖) := by
  have hseries : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 1| ^ (11 / 8 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 1 (11 / 8)).mpr (by norm_num)
  have hmajor : Summable (fun n : ℕ =>
      3 / (((n : ℝ) + 1) ^ (11 / 8 : ℝ))) := by
    have hcongr :
        (fun n : ℕ => 3 / (((n : ℝ) + 1) ^ (11 / 8 : ℝ))) =
          (fun n : ℕ => 3 * (1 / |(n : ℝ) + 1| ^ (11 / 8 : ℝ))) := by
      funext n
      rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
      ring
    rw [hcongr]
    exact hseries.mul_left 3
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
  · exact regularizedBaseCoeff_weighted_le
  · exact hmajor

#assert_trust kernel regularizedBaseCoeff_recurrence
#assert_trust kernel regularizedBaseCoeff_zero
#assert_trust kernel regularizedBaseCoeff_one
#assert_trust kernel regularizedBaseCoeff_two
#assert_trust kernel summable_regularizedBaseCoeff_weighted
#print axioms summable_regularizedBaseCoeff_weighted

end NLA.Proofs.SP14
