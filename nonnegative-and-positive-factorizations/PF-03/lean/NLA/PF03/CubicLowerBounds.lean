import NLA.PF03.CubicFiniteArithmetic

/-!
Exact rational lower bounds consume the accepted alpha enclosure, including
its kernel-mode LeanCert endpoint proofs. No new interval search is required.
Original mathematics and seed: Sidney Holden, Flatiron Institute, Simons Foundation.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology; Codex assistance.
-/
set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

def signedRationalLower (q l u : ℚ) : ℚ :=
  if 0 ≤ q then q * l else q * u

theorem signedRationalLower_le (q l u : ℚ) (x : ℝ)
    (hl : (l : ℝ) ≤ x) (hu : x ≤ (u : ℝ)) :
    (signedRationalLower q l u : ℝ) ≤ (q : ℝ) * x := by
  by_cases hq : 0 ≤ q
  · simp only [signedRationalLower, if_pos hq, Rat.cast_mul]
    exact mul_le_mul_of_nonneg_left hl (by exact_mod_cast hq)
  · simp only [signedRationalLower, if_neg hq, Rat.cast_mul]
    have hq0 : (q : ℝ) ≤ 0 := by exact_mod_cast (lt_of_not_ge hq).le
    exact mul_le_mul_of_nonpos_left hu hq0

def cubicLower (x : Cubic) : ℚ :=
  x 0 + signedRationalLower (x 1) ell upp +
    signedRationalLower (x 2) (ell ^ 2) (upp ^ 2)

theorem cubicLower_le (x : Cubic) : (cubicLower x : ℝ) ≤ cubicEval x := by
  have h₁ := signedRationalLower_le (x 1) ell upp alpha
    alpha_certificate.2.2.1.le alpha_certificate.2.2.2.le
  have hl₂ : ((ell ^ 2 : ℚ) : ℝ) ≤ alpha ^ 2 := by
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ root_lower_positive.le alpha_certificate.2.2.1.le 2
  have hu₂ : alpha ^ 2 ≤ ((upp ^ 2 : ℚ) : ℝ) := by
    rw [Rat.cast_pow]
    exact pow_le_pow_left₀ alpha_certificate.2.1.le alpha_certificate.2.2.2.le 2
  have h₂ := signedRationalLower_le (x 2) (ell ^ 2) (upp ^ 2) (alpha ^ 2) hl₂ hu₂
  simpa only [cubicLower, cubicEval, Rat.cast_add] using
    add_le_add (add_le_add le_rfl h₁) h₂

theorem cubicEval_pos_of_lower (x : Cubic) (hx : 0 < cubicLower x) :
    0 < cubicEval x :=
  lt_of_lt_of_le (by exact_mod_cast hx) (cubicLower_le x)

#print axioms cubicEval_pos_of_lower
#assert_trust kernel cubicEval_pos_of_lower

end NLA.PF03
