import DefinedTarget
import LeanCert.Tactic.Verification
set_option autoImplicit false
set_option leancert.trust "kernel"

open Lean Elab Command in
elab "#assert_proof_constant " n:ident : command => do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  match (← getEnv).find? decl with
  | some (.thmInfo _) => pure ()
  | _ => throwErrorAt n "expected a proved theorem constant"

#assert_proof_constant target
#assert_trust kernel target
#print axioms target
