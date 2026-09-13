/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact scalar minorant on the witness's spectral set. This is scalar
domination, not an operator-monotonicity assertion about the kink function.
-/
import NLA.RA08.Definitions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.RA08

theorem minorant_shift_identity (z : ℝ) :
    1 - minorantFunction (witnessA + z) =
      z * ((19 / 17 : ℝ) + (537952 / 23409 : ℝ) * z +
        (2069504 / 23409 : ℝ) * z ^ 2 +
        (288428032 / 1896129 : ℝ) * z ^ 3 +
        (227540992 / 1896129 : ℝ) * z ^ 4 +
        (67108864 / 1896129 : ℝ) * z ^ 5) := by
  norm_num [minorantFunction, minorantCoefficient, witnessA, witnessB]
  ring

theorem minorant_scalar_proved (x : ℝ) (_hx : 0 ≤ x)
    (hgap : x ≤ 1 ∨ witnessA ≤ x) : minorantFunction x ≤ witnessFunction x := by
  rcases hgap with hlow | hhigh
  · rw [witnessFunction, min_eq_left hlow]
    unfold minorantFunction
    have h : 0 ≤ minorantCoefficient * x ^ 2 * (x - 1 / 2) ^ 2 *
        (x - witnessB) ^ 2 := by
      unfold minorantCoefficient
      positivity
    linarith
  · have hz : 0 ≤ x - witnessA := sub_nonneg.mpr hhigh
    have hp : 0 ≤ (x - witnessA) * ((19 / 17 : ℝ) +
        (537952 / 23409 : ℝ) * (x - witnessA) +
        (2069504 / 23409 : ℝ) * (x - witnessA) ^ 2 +
        (288428032 / 1896129 : ℝ) * (x - witnessA) ^ 3 +
        (227540992 / 1896129 : ℝ) * (x - witnessA) ^ 4 +
        (67108864 / 1896129 : ℝ) * (x - witnessA) ^ 5) := by positivity
    have hi := minorant_shift_identity (x - witnessA)
    rw [add_sub_cancel] at hi
    have hx1 : 1 ≤ x := by norm_num [witnessA] at hhigh; linarith
    rw [witnessFunction, min_eq_right hx1]
    linarith

#assert_trust kernel minorant_shift_identity
#assert_trust kernel minorant_scalar_proved
#print axioms minorant_shift_identity
#print axioms minorant_scalar_proved

end NLA.RA08
