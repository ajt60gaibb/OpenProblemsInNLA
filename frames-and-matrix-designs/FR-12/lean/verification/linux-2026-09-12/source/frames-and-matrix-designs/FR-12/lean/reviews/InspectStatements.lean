/- Author inspection of elaborated statements; no proof implementation. -/
import Challenge
import LeanCert.Tactic.Verification

set_option leancert.trust "kernel"
set_option pp.proofs false

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

#check NLA.FR12.counting_semantics
#check NLA.FR12.injective_doubling
#check NLA.FR12.factorial_doubling
#check NLA.FR12.power_two_nonempty
#check NLA.FR12.power_two_lower_bound
#check NLA.FR12.counterexample
#check NLA.FR12.not_countingConjecture
#check Matrix.IsHadamard
#check Matrix.IsHadamard.of_mul_conjTranspose
#check Nat.factorial_mul_pow_sub_le_factorial
