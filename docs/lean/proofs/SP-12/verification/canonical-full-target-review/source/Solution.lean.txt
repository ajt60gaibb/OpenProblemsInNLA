import NLA.Proofs.SP12.Final

/-! Complete unchanged SP-12 target, discharged by the exact copied proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP12

theorem target : NLA.Statements.SP12.Target := by
  exact NLA.Proofs.SP12.target

#assert_trust kernel target
#print axioms target

end NLA.SP12
