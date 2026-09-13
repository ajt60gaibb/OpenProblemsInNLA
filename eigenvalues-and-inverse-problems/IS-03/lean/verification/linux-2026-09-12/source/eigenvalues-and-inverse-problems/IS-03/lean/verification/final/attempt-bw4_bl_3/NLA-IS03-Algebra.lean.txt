/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact polynomial certificates for Colbrook's IS-03 counterexample.
-/
import NLA.IS03.Definitions
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Matrix Polynomial
open scoped Matrix
namespace NLA.IS03

/-- A small exact Bézout certificate proves separability, without any spectral premise. -/
theorem derivativePolynomial_separable : derivativePolynomial.Separable := by
  rw [Polynomial.separable_def']
  refine ⟨C (7/542064 : ℝ) *
      (C 544126 - C 279851 * X + C 209536 * X^2 - C 24579 * X^3 - C 2909046 * X^4),
    C (7/542064 : ℝ) *
      (-C 2062 - C 276647 * X + C 55183 * X^2 - C 163022 * X^3 - C 30535 * X^4 + C 484841 * X^5), ?_⟩
  apply Polynomial.funext
  intro x
  norm_num [derivativePolynomial, Polynomial.derivative_add, Polynomial.derivative_sub,
    Polynomial.derivative_mul, Polynomial.derivative_pow]
  ring

theorem derivativePolynomial_monic : derivativePolynomial.Monic := by
  unfold derivativePolynomial
  monicity <;> norm_num

theorem derivativePolynomial_degree : derivativePolynomial.natDegree = 6 := by
  unfold derivativePolynomial
  compute_degree!

theorem nonnegative_power_trace_proved {n : ℕ} (A : RealMatrix n)
    (hA : EntrywiseNonnegative A) (k : ℕ) :
    EntrywiseNonnegative (A^k) ∧ 0 ≤ Matrix.trace (A^k) := by
  have hp := Matrix.pow_apply_nonneg hA k
  exact ⟨hp, Finset.sum_nonneg (fun i _ => hp i i)⟩

theorem witness_admissible_proved :
    EntrywiseNonnegative witnessMatrix ∧ Matrix.trace witnessMatrix = 1/2 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessMatrix]
  · norm_num [Matrix.trace, witnessMatrix, Fin.sum_univ_succ]

end NLA.IS03
