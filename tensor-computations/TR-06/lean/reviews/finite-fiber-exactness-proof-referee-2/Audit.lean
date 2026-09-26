import NLA.TR06.FiniteFiberExactness
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.TR06.FiniteFiber
example : RankBoundStatement := rank_bound_statement
example : SplitFamilyStatement := split_family_statement
example : UnitTensorStatement := unit_tensor_statement
example : CancelFamilyStatement := cancel_family_statement
example : ShorterInfiniteStatement := shorter_infinite_statement
example : ExactRankStatement := exact_rank_statement
#print axioms rank_bound_statement
#assert_trust kernel rank_bound_statement
#print axioms rankAtMostOne_smul
#assert_trust kernel rankAtMostOne_smul
#print axioms unit_tensor_statement
#assert_trust kernel unit_tensor_statement
#print axioms splitTuple_injective
#assert_trust kernel splitTuple_injective
#print axioms sum_splitTuple
#assert_trust kernel sum_splitTuple
#print axioms split_family_statement
#assert_trust kernel split_family_statement
#print axioms cancelTuple_injective
#assert_trust kernel cancelTuple_injective
#print axioms sum_cancelTuple
#assert_trust kernel sum_cancelTuple
#print axioms cancel_family_statement
#assert_trust kernel cancel_family_statement
#print axioms shorter_infinite_statement
#assert_trust kernel shorter_infinite_statement
#print axioms exact_rank_statement
#assert_trust kernel exact_rank_statement
#print axioms NLA.TR06.Segre.pureTensor_smul_mode
#assert_trust kernel NLA.TR06.Segre.pureTensor_smul_mode
end NLA.TR06.FiniteFiber
