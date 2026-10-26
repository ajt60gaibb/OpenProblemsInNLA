import NLA.Proofs.TR14.Final

/-! Complete unchanged TR-14 target, discharged by the exact copied proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.TR14

theorem target : NLA.Statements.TR14.Target := by
  exact NLA.Proofs.TR14.target

#assert_trust kernel target
#print axioms target

end NLA.TR14
