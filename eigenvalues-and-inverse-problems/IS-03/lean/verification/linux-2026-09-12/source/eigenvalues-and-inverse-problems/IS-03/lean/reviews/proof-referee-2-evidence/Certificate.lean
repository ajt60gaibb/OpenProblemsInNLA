/- Independent referee-only certificate inspection, not a project theorem.
The literal arguments below were read from the freshly elaborated proof term.
One declaration checks identity with the actual retained helper; the other
recomputes its Boolean result with the Lean kernel, without interval_decide. -/
import Solution

set_option leancert.trust "kernel"
namespace IndependentIS03Referee2

/-- The retained certificate has this exact expression, interval and configuration. -/
theorem retained_input_identity : LeanCert.Validity.checkStrictUpperBoundDyadicChecked
    ((LeanCert.Core.Expr.const (Rat.divInt 8593 1)).neg.mul
      (LeanCert.Core.Expr.const (Rat.divInt 1 823543)))
    (Rat.divInt 0 1) (Rat.divInt 0 1) (le_refl (Rat.divInt 0 1))
    (Rat.divInt 0 1) (-53) 10 = true :=
  NLA.IS03.numerical_negative_moment._proof_1_7

/-- Repeat only that exact finite check, using kernel reduction. -/
theorem exact_boolean_again : LeanCert.Validity.checkStrictUpperBoundDyadicChecked
    ((LeanCert.Core.Expr.const (Rat.divInt 8593 1)).neg.mul
      (LeanCert.Core.Expr.const (Rat.divInt 1 823543)))
    (Rat.divInt 0 1) (Rat.divInt 0 1) (le_refl (Rat.divInt 0 1))
    (Rat.divInt 0 1) (-53) 10 = true := by
  decide +kernel

#assert_trust kernel retained_input_identity
#print axioms retained_input_identity
#assert_trust kernel exact_boolean_again
#print axioms exact_boolean_again
set_option pp.proofs true in
#print retained_input_identity
set_option pp.proofs true in
#print exact_boolean_again
end IndependentIS03Referee2
