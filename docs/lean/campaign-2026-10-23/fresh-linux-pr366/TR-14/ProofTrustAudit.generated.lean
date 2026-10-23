import Solution
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#assert_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected a proved theorem constant"

#assert_proof_constant NLA.TR14.target
#assert_trust kernel NLA.TR14.target
#print axioms NLA.TR14.target
