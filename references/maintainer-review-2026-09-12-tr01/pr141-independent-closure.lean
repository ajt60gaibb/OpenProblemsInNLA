import Problem56.PaperV7.Certification
import Lean

open Lean Elab Command

namespace ReviewerAudit
private def dependencies (ci : ConstantInfo) : Array Name := Id.run do
  let mut out := ci.type.getUsedConstants
  match ci with
  | .defnInfo x => out := out ++ x.value.getUsedConstants
  | .thmInfo x => out := out ++ x.value.getUsedConstants
  | .opaqueInfo x => out := out ++ x.value.getUsedConstants
  | .inductInfo x => out := out ++ x.ctors.toArray
  | .recInfo x =>
    out := out ++ x.all.toArray
    for r in x.rules do out := out ++ #[r.ctor] ++ r.rhs.getUsedConstants
  | _ => pure ()
  return out

partial def walk (env : Environment) (todo : List Name) (seen : NameSet) :
    CommandElabM NameSet := do
  match todo with
  | [] => return seen
  | n :: rest =>
    if seen.contains n then return ← walk env rest seen
    let some ci := env.find? n | throwError "Missing declaration: {n}"
    if ci.isUnsafe then throwError "Unsafe declaration in final closure: {n}"
    if ci.isPartial then throwError "Partial declaration in final closure: {n}"
    if let .axiomInfo _ := ci then
      unless [``propext, ``Classical.choice, ``Quot.sound].contains n do
        throwError "Unexpected axiom in final closure: {n}"
    return ← walk env ((dependencies ci).toList ++ rest) (seen.insert n)

elab "#reviewer_closure " n:ident : command => do
  let target ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo n
  let env ← getEnv
  let some ci := env.find? target | throwError "Missing final theorem"
  unless ci.isTheorem do throwError "Final declaration is not a theorem"
  let seen ← walk env [target] {}
  logInfo m!"REVIEWER_CLOSURE|{target}|{seen.size}|no unsafe or partial dependencies; only three permitted axioms"

#reviewer_closure Problem56.PaperV7.certified_main
#reviewer_closure Problem56.PaperV7.certified_explicit_main
#reviewer_closure Problem56.PaperV7.main_prescribed_width_ose
end ReviewerAudit
