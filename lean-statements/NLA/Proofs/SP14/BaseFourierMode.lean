import NLA.Statements.SP14
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
Exact orthogonality for individual integer circle modes under the frozen
SP-14 real-interval Fourier coefficient. Termwise integration of the
infinite base-symbol series remains a separate analytic obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private theorem normalized_exp_mode (d : ℤ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (((d : ℂ) * Complex.I) * (t : ℂ))) =
      if d = 0 then 1 else 0 := by
  by_cases hd : d = 0
  · subst d
    simp only [Int.cast_zero, zero_mul, Complex.exp_zero, ite_true]
    simp
    have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hp]
  · have hc : (d : ℂ) * Complex.I ≠ 0 :=
      mul_ne_zero (Int.cast_ne_zero.mpr hd) Complex.I_ne_zero
    have hperiod :
        Complex.exp (((d : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I d using 1
      push_cast
      ring_nf
    push_cast at hperiod
    rw [integral_exp_mul_complex (a := (0 : ℝ))
      (b := 2 * Real.pi) hc]
    simp [hd, hperiod]

/-- The frozen SP-14 Fourier integral gives exactly one at the matching
integer circle mode and zero at every other integer frequency. -/
theorem FourierCoefficient_circle_mode (ell k : ℤ) :
    FourierCoefficient (fun z : Circle => (z : ℂ) ^ ell) k =
      if ell = k then 1 else 0 := by
  have hintegrand (t : ℝ) :
      (Circle.exp t : ℂ) ^ ell *
        Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ))) =
      Complex.exp ((((ell - k : ℤ) : ℂ) * Complex.I) * (t : ℂ)) := by
    rw [Circle.coe_exp, ← Complex.exp_int_mul]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold FourierCoefficient
  simp_rw [hintegrand]
  rw [normalized_exp_mode (ell - k)]
  simp only [sub_eq_zero]

#assert_trust kernel FourierCoefficient_circle_mode
#print axioms FourierCoefficient_circle_mode

end NLA.Proofs.SP14
