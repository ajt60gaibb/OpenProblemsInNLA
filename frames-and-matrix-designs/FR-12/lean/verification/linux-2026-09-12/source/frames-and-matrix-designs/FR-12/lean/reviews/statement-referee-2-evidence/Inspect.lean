/- Independent statement referee 2 inspection. No proof implementation.
Reviewer: Codex agent /root/leancert_examples, independent of the author. -/
import Challenge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"

set_option pp.explicit true in
#print NLA.FR12.IsRealHadamard
set_option pp.explicit true in
#print NLA.FR12.HadamardMatrices
set_option pp.explicit true in
#print NLA.FR12.hadamardCount
set_option pp.explicit true in
#print NLA.FR12.CountingConjecture
set_option pp.explicit true in
#print NLA.FR12.doublingMatrix
set_option pp.explicit true in
#print NLA.FR12.doublingMap
set_option pp.explicit true in
#check NLA.FR12.power_two_lower_bound
set_option pp.explicit true in
#check NLA.FR12.counterexample

#check NLA.FR12.counting_semantics
#check NLA.FR12.injective_doubling
#check NLA.FR12.factorial_doubling
#check NLA.FR12.power_two_nonempty
#check NLA.FR12.not_countingConjecture
#check Matrix.IsHadamard.of_mul_conjTranspose
#check Unitary.mem_iff_eq_one_or_eq_neg_one
#check Nat.card_le_card_of_injective
#check Nat.factorial_mul_pow_sub_le_factorial
#check Real.log_pow
#check Real.rpow_natCast

#assert_trust kernel NLA.FR12.IsRealHadamard
#assert_trust kernel NLA.FR12.HadamardMatrices
#assert_trust kernel NLA.FR12.hadamardCount
#assert_trust kernel NLA.FR12.CountingConjecture
#assert_trust kernel NLA.FR12.doublingMatrix
#assert_trust kernel NLA.FR12.doublingMap
#print axioms NLA.FR12.IsRealHadamard
#print axioms NLA.FR12.HadamardMatrices
#print axioms NLA.FR12.hadamardCount
#print axioms NLA.FR12.CountingConjecture
#print axioms NLA.FR12.doublingMatrix
#print axioms NLA.FR12.doublingMap
