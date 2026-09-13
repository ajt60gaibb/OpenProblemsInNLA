/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Mathematical transfer theorem: Matthew J. Colbrook.

The selected-zero-column inequality retains the actual f(0) contribution.
-/
import NLA.RA09.Definitions
import LeanCert.Tactic.Verification
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.RA09

theorem zero_column_average_proved {n : ℕ} (a p : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (f : ℝ → ℝ) (hf : AdmissibleFunction f) (τ : ℝ) :
    (f 0)^2 - 2*f 0*(∑ i, p i*f (a i)) ≤
      ∑ i, p i * scalarAuxiliary f τ (a i) := by
  have hf0 : 0 ≤ f 0 := hf.2.2.2 0 le_rfl
  have havg : f 0 ≤ ∑ i, p i * f (a i) := by
    calc
      f 0 = ∑ i, p i * f 0 := by rw [← Finset.sum_mul, hsum, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hf.2.2.1 (by simp) (ha i) (ha i)) (hp i)
  have haux : 0 ≤ ∑ i, p i * scalarAuxiliary f τ (a i) := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (le_max_right _ _)
  have hweighted := mul_nonneg hf0 (sub_nonneg.mpr havg)
  nlinarith [sq_nonneg (f 0)]

#assert_trust kernel zero_column_average_proved
#print axioms zero_column_average_proved

end NLA.RA09
