/- Root independently inspects the retained fresh certificate term and repeats
its exact Boolean checker input with explicit kernel reduction. -/
import Solution

set_option pp.all true in
#print NLA.IV06.numerical_separator_margin._proof_1_7
#assert_trust kernel NLA.IV06.numerical_separator_margin._proof_1_7
#print axioms NLA.IV06.numerical_separator_margin._proof_1_7

example : LeanCert.Validity.checkStrictUpperBoundDyadicChecked
    (LeanCert.Core.Expr.const (Rat.divInt 18 1)).neg
    (Rat.divInt 0 1) (Rat.divInt 0 1) (le_refl (Rat.divInt 0 1))
    (Rat.divInt 0 1) (-53) 10 = true := by
  decide +kernel
