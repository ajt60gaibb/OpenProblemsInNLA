import Mathlib.Analysis.SpecialFunctions.Exp

/-! ## KernelTaylorBounds -/

section

set_option autoImplicit false
noncomputable section
open Real

namespace NLA.FR05

theorem exp_quadratic_remainder (x : ℝ) :
    |Real.exp x - 1 - x| ≤ |x| ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  norm_num [Finset.sum_range_succ] at h
  simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, sub_add_eq_sub_sub, sq_abs] using h

theorem exp_cubic_remainder (x : ℝ) :
    |Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)| ≤ |x| ^ 4 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 4
  norm_num [Finset.sum_range_succ] at h
  convert h using 1
  simp only [← Complex.ofReal_exp, ← Complex.ofReal_one,
    ← Complex.ofReal_add, ← Complex.ofReal_pow, ← Complex.ofReal_div,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem cosh_quadratic_remainder (x : ℝ) :
    |Real.cosh x - 1 - x ^ 2 / 2| ≤ |x| ^ 4 * Real.exp |x| := by
  have hpos := exp_cubic_remainder x
  have hneg := exp_cubic_remainder (-x)
  simp only [abs_neg, neg_sq] at hneg
  have he : Real.cosh x - 1 - x ^ 2 / 2 =
      ((Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6)) +
        (Real.exp (-x) - (1 + -x + (-x) ^ 2 / 2 + (-x) ^ 3 / 6))) / 2 := by
    rw [Real.cosh_eq]
    ring
  rw [he, abs_div]
  norm_num
  have ht := abs_add_le
    (Real.exp x - (1 + x + x ^ 2 / 2 + x ^ 3 / 6))
    (Real.exp (-x) - (1 + -x + (-x) ^ 2 / 2 + (-x) ^ 3 / 6))
  simp only [neg_sq] at ht
  nlinarith

theorem exp_difference_bound (x y : ℝ) :
    |Real.exp x - Real.exp y| ≤ |x - y| * Real.exp (max x y) := by
  wlog hxy : y ≤ x generalizing x y
  · simpa only [abs_sub_comm, max_comm] using this y x (le_of_not_ge hxy)
  rw [max_eq_left hxy, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hxy)),
    abs_of_nonneg (sub_nonneg.mpr hxy)]
  have h := Real.add_one_le_exp (y - x)
  have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos x).le
  rw [← Real.exp_add] at hmul
  have he : x + (y - x) = y := by ring
  rw [he] at hmul
  nlinarith

theorem polynomial_exp_eighth_bound {T : ℝ} (hT : 0 ≤ T) :
    (1 + T) ^ 4 * Real.exp (T / 8) ≤
      (24 * 8 ^ 4 * Real.exp (1 / 8)) * Real.exp (T / 4) := by
  have h := Real.pow_div_factorial_le_exp ((1 + T) / 8) (by positivity) 4
  norm_num at h
  have he : Real.exp ((1 + T) / 8) * Real.exp (T / 8) =
      Real.exp (1 / 8) * Real.exp (T / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hh := mul_le_mul_of_nonneg_right h (Real.exp_pos (T / 8)).le
  rw [he] at hh
  nlinarith

end NLA.FR05

end

end

/-! ## KernelEvenTaylor -/

section

set_option autoImplicit false
noncomputable section
open Real

namespace NLA.FR05

def kernelEvenExp (A B : ℝ) : ℝ := (Real.exp (-A + B) + Real.exp (-A - B)) / 2

/-- Factor the even exponential as `exp (-A) * cosh B` and estimate the two
remainders at their respective quadratic and quartic orders. -/
theorem kernelEvenExp_factor_bound (A B : ℝ) :
    |kernelEvenExp A B - (1 - A + B ^ 2 / 2)| ≤
      (B ^ 4 + A ^ 2 + |A| * B ^ 2 / 2) * Real.exp (|A| + |B|) := by
  have he : kernelEvenExp A B - (1 - A + B ^ 2 / 2) =
      Real.exp (-A) * (Real.cosh B - 1 - B ^ 2 / 2) +
        (Real.exp (-A) - 1 + A) + (Real.exp (-A) - 1) * B ^ 2 / 2 := by
    simp only [kernelEvenExp, Real.cosh_eq, Real.exp_add, Real.exp_sub]
    rw [Real.exp_neg B]
    ring
  have hA := exp_quadratic_remainder (-A)
  simp only [sub_neg_eq_add, abs_neg, sq_abs] at hA
  have hD : |Real.exp (-A) - 1| ≤ |A| * Real.exp (|A| + |B|) := by
    have h := exp_difference_bound (-A) 0
    simp only [Real.exp_zero, sub_zero, abs_neg] at h
    apply h.trans
    gcongr
    exact max_le (by linarith [neg_le_abs A, abs_nonneg B]) (by positivity)
  have hB : Real.exp (-A) * |Real.cosh B - 1 - B ^ 2 / 2| ≤
      B ^ 4 * Real.exp (|A| + |B|) := by
    calc
      _ ≤ Real.exp |A| * (|B| ^ 4 * Real.exp |B|) := by
        gcongr
        · exact neg_le_abs A
        · exact cosh_quadratic_remainder B
      _ = _ := by
        rw [Real.exp_add, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ B ^ 4)]
        ring
  have hA' : |Real.exp (-A) - 1 + A| ≤ A ^ 2 * Real.exp (|A| + |B|) := by
    apply hA.trans
    gcongr
    exact le_add_of_nonneg_right (abs_nonneg B)
  rw [he]
  calc
    _ ≤ |Real.exp (-A) * (Real.cosh B - 1 - B ^ 2 / 2)| +
        |Real.exp (-A) - 1 + A| + |(Real.exp (-A) - 1) * B ^ 2 / 2| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      simp only [abs_mul, abs_of_pos (Real.exp_pos _), abs_div,
        abs_of_nonneg (sq_nonneg B), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      nlinarith [mul_le_mul_of_nonneg_right hD (sq_nonneg B)]

end NLA.FR05

end

end

/-! ## KernelScalarRemainder -/

section

set_option autoImplicit false
noncomputable section
open Real

namespace NLA.FR05

theorem kernel_radius_power_bound {T : ℝ} (hT : 0 ≤ T) (k : ℕ) (hk : k ≤ 4) :
    T ^ k ≤ (1 + T) ^ 4 := by
  calc
    _ ≤ (1 + T)^k := by gcongr; linarith
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hk

/-- The separated exponential/cosh estimate improves the former constant 5000
to 304, with the same radius and hypotheses. -/
theorem kernel_even_exp_remainder {ρ T A B : ℝ}
    (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 128) (hT : 0 ≤ T)
    (hA : |A| ≤ 4 * ρ ^ 2 * T) (hB : |B| ≤ 4 * ρ * T) :
    |kernelEvenExp A B - (1 - A + B ^ 2 / 2)| ≤
      304 * ρ ^ 4 * (1 + T) ^ 4 * Real.exp (T / 8) := by
  have hρ2 : ρ ^ 2 ≤ ρ := by nlinarith
  have hS : |A| + |B| ≤ T / 8 := by
    nlinarith [mul_le_mul_of_nonneg_right hρ2 hT,
      mul_le_mul_of_nonneg_right hρsmall hT]
  have hpoly : B ^ 4 + A ^ 2 + |A| * B ^ 2 / 2 ≤
      304 * ρ ^ 4 * (1 + T) ^ 4 := by
    calc
      _ = |B| ^ 4 + |A| ^ 2 + |A| * |B| ^ 2 / 2 := by
        rw [← abs_pow, abs_of_nonneg (by positivity : 0 ≤ B ^ 4), sq_abs, sq_abs]
      _ ≤ (4 * ρ * T) ^ 4 + (4 * ρ ^ 2 * T) ^ 2 +
          (4 * ρ ^ 2 * T) * (4 * ρ * T) ^ 2 / 2 := by gcongr
      _ = ρ ^ 4 * (256 * T ^ 4 + 16 * T ^ 2 + 32 * T ^ 3) := by ring
      _ ≤ ρ ^ 4 * (256 * (1 + T) ^ 4 + 16 * (1 + T) ^ 4 +
          32 * (1 + T) ^ 4) := by
        gcongr
        · linarith
        · exact kernel_radius_power_bound hT 2 (by lia)
        · exact kernel_radius_power_bound hT 3 (by lia)
      _ = _ := by ring
  exact (kernelEvenExp_factor_bound A B).trans
    (mul_le_mul hpoly (Real.exp_le_exp.mpr hS) (Real.exp_pos _).le (by positivity))


theorem kernel_scalar_remainder {ρ T A B D E F L : ℝ}
    (hρ : 0 ≤ ρ) (hρsmall : ρ ≤ 1 / 128) (hT : 0 ≤ T)
    (hD0 : 0 ≤ D) (hD : D ≤ 2) (hDdiff : |D - 1| ≤ 4 * ρ^2)
    (hD2 : |D - 1 - F| ≤ 16 * ρ^4)
    (hA : |A| ≤ 4 * ρ^2 * T) (hAE : |A - E| ≤ 6 * ρ^4 * T)
    (hB : |B| ≤ 4 * ρ * T) (hBL : |B - L| ≤ 10 * ρ^3 * T)
    (hL : |L| ≤ ρ * T) :
    |D * kernelEvenExp A B - (1 + F - E + L^2 / 2)| ≤
      11000 * ρ^4 * (1 + T)^4 * Real.exp (T / 8) := by
  have hDA : |D * A - E| ≤ 22 * ρ^4 * T := by
    calc
      _ = |(D - 1) * A + (A - E)| := by congr 1; ring
      _ ≤ |(D - 1) * A| + |A - E| := abs_add_le _ _
      _ = |D - 1| * |A| + |A - E| := by rw [abs_mul]
      _ ≤ (4 * ρ^2) * (4 * ρ^2 * T) + 6 * ρ^4 * T := by gcongr
      _ = _ := by ring
  have hBsq : B^2 ≤ 16 * ρ^2 * T^2 := by
    have := pow_le_pow_left₀ (abs_nonneg B) hB 2
    rw [sq_abs] at this
    nlinarith
  have hDB : |D * B^2 - L^2| ≤ 114 * ρ^4 * T^2 := by
    calc
      _ = |(D - 1) * B^2 + (B - L) * (B + L)| := by congr 1; ring
      _ ≤ |(D - 1) * B^2| + |(B - L) * (B + L)| := abs_add_le _ _
      _ = |D - 1| * B^2 + |B - L| * |B + L| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg B)]
      _ ≤ (4 * ρ^2) * (16 * ρ^2 * T^2) +
          (10 * ρ^3 * T) * (5 * ρ * T) := by
        gcongr
        exact (abs_add_le B L).trans (by linarith)
      _ = _ := by ring
  have hTaylor := kernel_even_exp_remainder hρ hρsmall hT hA hB
  have hfirst : |D * (kernelEvenExp A B - (1 - A + B^2 / 2))| ≤
      608 * ρ^4 * (1 + T)^4 * Real.exp (T / 8) := by
    rw [abs_mul, abs_of_nonneg hD0]
    calc
      _ ≤ 2 * (304 * ρ^4 * (1 + T)^4 * Real.exp (T / 8)) :=
        mul_le_mul hD hTaylor (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hpoly : |D * (1 - A + B^2 / 2) - (1 + F - E + L^2 / 2)| ≤
      16 * ρ^4 + 22 * ρ^4 * T + 57 * ρ^4 * T^2 := by
    calc
      _ = |((D - 1 - F) - (D * A - E)) + (D * B^2 - L^2) / 2| := by congr 1; ring
      _ ≤ |(D - 1 - F) - (D * A - E)| + |(D * B^2 - L^2) / 2| := abs_add_le _ _
      _ ≤ (|D - 1 - F| + |D * A - E|) + |(D * B^2 - L^2) / 2| := by
        gcongr
        exact abs_sub _ _
      _ ≤ _ := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
  have hExp : 1 ≤ Real.exp (T / 8) := Real.one_le_exp (by positivity)
  have hQ0 : ρ^4 ≤ ρ^4 * (1 + T)^4 * Real.exp (T / 8) := by
    calc
      _ ≤ ρ^4 * (1 + T)^4 := le_mul_of_one_le_right (by positivity) (by nlinarith [kernel_radius_power_bound hT 0 (by lia)])
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  have hQ1 : ρ^4 * T ≤ ρ^4 * (1 + T)^4 * Real.exp (T / 8) := by
    calc
      _ ≤ ρ^4 * (1 + T)^4 := by
        gcongr
        simpa only [pow_one] using kernel_radius_power_bound hT 1 (by lia)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  have hQ2 : ρ^4 * T^2 ≤ ρ^4 * (1 + T)^4 * Real.exp (T / 8) := by
    calc
      _ ≤ ρ^4 * (1 + T)^4 := by
        gcongr
        exact kernel_radius_power_bound hT 2 (by lia)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hExp
  have hfinal : |D * kernelEvenExp A B - (1 + F - E + L^2 / 2)| ≤
      |D * (kernelEvenExp A B - (1 - A + B^2 / 2))| +
        |D * (1 - A + B^2 / 2) - (1 + F - E + L^2 / 2)| := by
    have he : D * kernelEvenExp A B - (1 + F - E + L^2 / 2) =
        D * (kernelEvenExp A B - (1 - A + B^2 / 2)) +
          (D * (1 - A + B^2 / 2) - (1 + F - E + L^2 / 2)) := by ring
    rw [he]
    exact abs_add_le _ _
  nlinarith [show 0 ≤ ρ^4 * (1 + T)^4 * Real.exp (T / 8) by positivity]

end NLA.FR05

end

end
