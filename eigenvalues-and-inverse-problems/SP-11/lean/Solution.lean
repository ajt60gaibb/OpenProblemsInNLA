import NLA.Proofs.SP11.Final

/-! Complete unchanged SP-11 target, discharged by the exact copied proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SP11

theorem target : NLA.Statements.SP11.Target := by
  exact NLA.Proofs.SP11.target

#assert_trust kernel target
#print axioms target

end NLA.SP11
