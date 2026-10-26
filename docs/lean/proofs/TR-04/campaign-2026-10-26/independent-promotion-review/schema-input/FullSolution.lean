import Solution
import NLA.Proofs.TR04.MachineTTFull
import NLA.Proofs.TR04.MachineTTRecursiveChild

/-! Complete original concrete Target and unchanged retained support exports.
Neither comparison Challenge module is imported by this solution. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.TR04

theorem target : NLA.Statements.TR04.Target := NLA.Proofs.TR04.fullTarget

end NLA.TR04

#assert_trust kernel candidate_count_le_first_mode
#assert_trust kernel cyclic_window_count_le_first_mode
#assert_trust kernel NLA.TR04.target
#print axioms candidate_count_le_first_mode
#print axioms cyclic_window_count_le_first_mode
#print axioms NLA.TR04.target
