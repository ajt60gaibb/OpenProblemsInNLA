/-
Formalization and mathematical proof: George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA. Substantial AI-agent assistance.
-/
import NLA.FR12.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section

namespace NLA.FR12

/-- The exact matrix set is finite in every dimension, and agrees with the
standard Mathlib Hadamard notion in every positive dimension. -/
theorem counting_semantics (n : ℕ) :
    Finite (HadamardMatrices n) ∧
    (∀ (_hn : 1 ≤ n) (A : Mat n), IsRealHadamard A ↔ A.IsHadamard) := by
  exact counting_semantics_proved n

/-- The restricted construction always gives a genuine labeled Hadamard matrix,
and the original pair and permutation are recoverable. No factorization or
injectivity assumption is an input. -/
theorem injective_doubling (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : HadamardMatrices m × HadamardMatrices m × Equiv.Perm (Fin m),
      IsRealHadamard (doublingMap m x)) ∧ Function.Injective (doublingMap m) := by
  exact injective_doubling_proved m hm

/-- Count the actual injective construction. The smaller factorial factor is
sufficient; the source's larger all-matching factor is not asserted here. -/
theorem factorial_doubling (m : ℕ) (hm : 1 ≤ m) :
    m.factorial * hadamardCount m ^ 2 ≤ hadamardCount (2 * m) := by
  exact factorial_doubling_proved m hm

/-- Positivity for every power-of-two order, required before taking logarithms. -/
theorem power_two_nonempty (k : ℕ) : 1 ≤ hadamardCount (2 ^ k) := by
  exact power_two_nonempty_proved k

/-- Exactly the manuscript's lower bound, with index shift k+2 to avoid
truncated natural subtraction. The outer exponent is real; the inner power uses the natural exponent k+2. -/
theorem power_two_lower_bound (k : ℕ) :
    (2 : ℝ) ^ ((2 : ℝ) ^ (k + 2) * (k : ℝ) * ((k : ℝ) + 1) / 8) ≤
      (hadamardCount (2 ^ (k + 2)) : ℝ) := by
  exact power_two_lower_bound_proved k

/-- Every proposed positive constant fails at a positive power-of-two multiple of four. -/
theorem counterexample (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ,
      (2 : ℝ) ^ (C * ((2 ^ (k + 2) : ℕ) : ℝ) *
        (Real.log ((2 ^ (k + 2) : ℕ) : ℝ) / Real.log 2)) <
          (hadamardCount (2 ^ (k + 2)) : ℝ) := by
  exact counterexample_proved C hC

/-- Full unconditional negation of the original labeled-matrix counting conjecture. -/
theorem not_countingConjecture : ¬ CountingConjecture := by
  exact not_countingConjecture_proved

#assert_trust kernel counting_semantics
#print axioms counting_semantics
#assert_trust kernel injective_doubling
#print axioms injective_doubling
#assert_trust kernel factorial_doubling
#print axioms factorial_doubling
#assert_trust kernel power_two_nonempty
#print axioms power_two_nonempty
#assert_trust kernel power_two_lower_bound
#print axioms power_two_lower_bound
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_countingConjecture
#print axioms not_countingConjecture

end NLA.FR12
