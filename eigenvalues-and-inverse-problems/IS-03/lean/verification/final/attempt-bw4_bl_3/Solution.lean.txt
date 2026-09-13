/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Complete proof exports matching the independently reviewed reference statements.
Formalization of Matthew J. Colbrook's counterexample; see verification/PROOF_MAP.md.
-/
import NLA.IS03.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IS03

/-- Nonnegative real matrices retain nonnegative entries and trace under every natural power. -/
theorem nonnegative_power_trace {n : ℕ} (A : RealMatrix n)
    (hA : EntrywiseNonnegative A) (k : ℕ) :
    EntrywiseNonnegative (A^k) ∧ 0 ≤ Matrix.trace (A^k) := by
  exact nonnegative_power_trace_proved A hA k

/-- The original witness is an admissible nonnegative matrix, with its genuine trace. -/
theorem witness_admissible :
    EntrywiseNonnegative witnessMatrix ∧ Matrix.trace witnessMatrix = 1/2 := by
  exact witness_admissible_proved

/-- Actual characteristic polynomial and formal derivative, including monicity and degree. -/
theorem witness_polynomials :
    witnessMatrix.charpoly = witnessPolynomial ∧
    normalizedDerivative 7 witnessMatrix.charpoly = derivativePolynomial ∧
    derivativePolynomial.Monic ∧ derivativePolynomial.natDegree = 6 := by
  exact witness_polynomials_proved

/-- Every potential real realization has exactly these traces, without spectral assumptions. -/
theorem trace_moment_certificate (B : RealMatrix 6)
    (hB : B.charpoly = derivativePolynomial) :
    ∀ i : Fin 7, Matrix.trace (B^(i.val + 1)) = traceMoments i := by
  exact trace_moment_certificate_proved B hB

/-- The exact seventh trace is negative; the planned LeanCert certificate must be consumed here. -/
theorem negative_moment :
    traceMoments 6 = (-8593/823543 : ℝ) ∧ traceMoments 6 < 0 := by
  exact negative_moment_proved

/-- The actual source matrix has no entrywise-nonnegative realization of its normalized derivative. -/
theorem counterexample :
    EntrywiseNonnegative witnessMatrix ∧
    ∀ B : RealMatrix 6, EntrywiseNonnegative B →
      B.charpoly ≠ normalizedDerivative 7 witnessMatrix.charpoly := by
  exact counterexample_proved

/-- Complete negative answer to the original all-dimension conjecture. -/
theorem not_derivativeRealizabilityConjecture :
    ¬ DerivativeRealizabilityConjecture := by
  exact not_derivativeRealizabilityConjecture_proved

#assert_trust kernel nonnegative_power_trace
#assert_trust kernel witness_admissible
#assert_trust kernel witness_polynomials
#assert_trust kernel trace_moment_certificate
#assert_trust kernel negative_moment
#assert_trust kernel counterexample
#assert_trust kernel not_derivativeRealizabilityConjecture
#print axioms nonnegative_power_trace
#print axioms witness_admissible
#print axioms witness_polynomials
#print axioms trace_moment_certificate
#print axioms negative_moment
#print axioms counterexample
#print axioms not_derivativeRealizabilityConjecture
end NLA.IS03
