/- Independent inspection and kernel reduction of the actual retained scalar
checker, after all candidate source modules have been rebuilt in a fresh prefix.+The candidate proof and its generated helper remain unchanged.
-/
import Solution

set_option pp.proofs true in
#print NLA.IS03.numerical_negative_moment._proof_1_7
#assert_trust kernel NLA.IS03.numerical_negative_moment._proof_1_7
#print axioms NLA.IS03.numerical_negative_moment._proof_1_7

theorem independently_reduced_actual_checker :
    LeanCert.Validity.checkStrictUpperBoundDyadicChecked
      ((LeanCert.Core.Expr.const (Rat.divInt 8593 1)).neg.mul
        (LeanCert.Core.Expr.const (Rat.divInt 1 823543)))
      (Rat.divInt 0 1) (Rat.divInt 0 1) (le_refl (Rat.divInt 0 1))
      (Rat.divInt 0 1) (-53) 10 = true := by
  decide +kernel

#assert_trust kernel independently_reduced_actual_checker
#print axioms independently_reduced_actual_checker
