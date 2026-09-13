/- Inspect the actual retained checker equality, separately from its consumer.
The helper name below was read from the freshly rebuilt numerical theorem. -/
import Solution

set_option pp.all true in
#print NLA.IV06.numerical_separator_margin._proof_1_7
#assert_trust kernel NLA.IV06.numerical_separator_margin._proof_1_7
#print axioms NLA.IV06.numerical_separator_margin._proof_1_7

-- This repeats exactly the retained checker input, using kernel reduction.
example : LeanCert.Validity.checkStrictUpperBoundDyadicChecked
    (LeanCert.Core.Expr.const (Rat.divInt 18 1)).neg
    (Rat.divInt 0 1) (Rat.divInt 0 1) (le_refl (Rat.divInt 0 1))
    (Rat.divInt 0 1) (-53) 10 = true := by
  decide +kernel
