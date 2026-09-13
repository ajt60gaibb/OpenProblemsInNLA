import Challenge
import LeanCert.Tactic.Verification
import Mathlib.Data.Fintype.Perm

set_option pp.universes true
set_option pp.explicit true

#print NLA.FR12.IsRealHadamard
#print NLA.FR12.HadamardMatrices
#print NLA.FR12.hadamardCount
#print NLA.FR12.CountingConjecture
#print NLA.FR12.doublingMatrix
#print NLA.FR12.doublingMap

#check NLA.FR12.counting_semantics
#check NLA.FR12.injective_doubling
#check NLA.FR12.factorial_doubling
#check NLA.FR12.power_two_nonempty
#check NLA.FR12.power_two_lower_bound
#check NLA.FR12.counterexample
#check NLA.FR12.not_countingConjecture

#print Matrix.IsHadamard
#check Matrix.IsHadamard.of_mul_conjTranspose
#print Matrix.reindex
#print Matrix.reindex_apply
#print finSumFinEquiv
#check finSumFinEquiv_apply_left
#check finSumFinEquiv_apply_right
#check Matrix.fromBlocks_apply₁₁
#check Matrix.fromBlocks_apply₁₂
#check Matrix.fromBlocks_apply₂₁
#check Matrix.fromBlocks_apply₂₂
#print Nat.card
#check Nat.card_eq_zero_of_infinite
#check Nat.card_pos_iff
#check Nat.card_le_card_of_injective
#check Nat.card_prod
#check Fintype.card_perm
#check Nat.factorial_mul_pow_sub_le_factorial
#check Real.log_pow
#check Real.rpow_lt_rpow_of_exponent_lt
#print Real.logb

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
#print axioms NLA.FR12.counting_semantics
#print axioms NLA.FR12.injective_doubling
#print axioms NLA.FR12.factorial_doubling
#print axioms NLA.FR12.power_two_nonempty
#print axioms NLA.FR12.power_two_lower_bound
#print axioms NLA.FR12.counterexample
#print axioms NLA.FR12.not_countingConjecture

set_option pp.all true in
#check NLA.FR12.power_two_lower_bound
set_option pp.all true in
#print NLA.FR12.CountingConjecture
set_option pp.all true in
#print NLA.FR12.doublingMatrix
