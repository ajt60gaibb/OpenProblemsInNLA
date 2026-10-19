import NLA.Proofs.PF05.Final
import Identity

/-! The complete unchanged PF-05 Target, after two independent canonical
boundary approvals. Challenge is a separate comparison environment. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.PF05

theorem target : NLA.Statements.PF05.Target := by
  exact NLA.Proofs.PF05.target

#assert_trust kernel target
#print axioms target
end NLA.PF05
