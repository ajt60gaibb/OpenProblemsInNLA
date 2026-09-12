/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's IE-19 counterexample.
-/
import NLA.IE19.Proof

set_option autoImplicit false
namespace NLA.IE19

theorem counterexample :
    Admissible 1 1 witness ∧
    IsUnit witness.det ∧
    IsUnit (comparisonMatrix (n := 3) 1 1).det ∧
    rowSumNorm witness⁻¹ = 7 / 9 ∧
    rowSumNorm (comparisonMatrix (n := 3) 1 1)⁻¹ = 5 / 4 ∧
    rowSumNorm witness⁻¹ < comparisonBound 3 1 1 :=
  counterexample_proved

theorem not_lowerBoundConjecture : ¬ LowerBoundConjecture :=
  not_lowerBoundConjecture_proved

theorem not_sharpConjecture : ¬ SharpConjecture :=
  not_sharpConjecture_proved

#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_lowerBoundConjecture
#print axioms not_lowerBoundConjecture
#assert_trust kernel not_sharpConjecture
#print axioms not_sharpConjecture

end NLA.IE19
