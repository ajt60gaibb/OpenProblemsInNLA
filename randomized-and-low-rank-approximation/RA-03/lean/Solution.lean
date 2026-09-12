/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization of Matthew J. Colbrook's counterexample to RA-03.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.RA03.Proof

set_option autoImplicit false
open scoped BigOperators Matrix.Norms.Frobenius

namespace NLA.RA03

theorem frobeniusSq_eq_norm_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) :
    frobeniusSq A = ‖A‖ ^ 2 :=
  frobeniusSq_eq_norm_sq_proved A

theorem process_isProbability {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (k : ℕ) :
    (∀ p : Pivot m n, 0 ≤ pivotMass A p) ∧
    (∑ p : Pivot m n, pivotMass A p) = 1 ∧
    (∀ h : Fin k → Pivot m n, 0 ≤ historyMass A h) ∧
    (∑ h : Fin k → Pivot m n, historyMass A h) = 1 :=
  process_isProbability_proved A k

theorem counterexample :
    witness ≠ 0 ∧ (∀ i j : Fin 2, witness i j ≠ 0) ∧
    frobeniusSq witness = 10 ∧
    witness.conjTranspose * witness = witnessGram ∧
    singularValue witness 0 = 3 ∧ singularValue witness 1 = 1 ∧
    (∀ i j : Fin 2, pivotMass witness (some (i, j)) = witnessPivotMass i j) ∧
    (∀ i j : Fin 2, frobeniusSq (pivotResidual witness (i, j)) = witnessPivotError i j) ∧
    expectedError witness 1 = 18 / 5 ∧ singularTailSq witness 1 = 1 ∧
    (2 : ℝ) ^ 1 * singularTailSq witness 1 < expectedError witness 1 :=
  counterexample_proved

theorem not_squaredErrorConjecture : ¬ SquaredErrorConjecture :=
  not_squaredErrorConjecture_proved

#assert_trust kernel frobeniusSq_eq_norm_sq
#print axioms frobeniusSq_eq_norm_sq
#assert_trust kernel process_isProbability
#print axioms process_isProbability
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_squaredErrorConjecture
#print axioms not_squaredErrorConjecture

end NLA.RA03
