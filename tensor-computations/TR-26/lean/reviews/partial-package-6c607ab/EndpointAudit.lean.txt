import Solution
import Reviewed.TR26
set_option leancert.trust "kernel"
open Lean Elab Command
elab "#package_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo name with
  | .thmInfo _ => pure ()
  | _ => throwError "package requires an actual theorem: {name}"
elab "#package_absent " target:ident : command => do
  if (← getEnv).contains target.getId then
    throwError "partial package unexpectedly contains {target.getId}"
#package_theorem NLA.Proofs.TR26.isotropic_degree
#package_absent NLA.Proofs.TR26.nonisotropic_degree
#package_absent NLA.Proofs.TR26.target
#assert_trust kernel NLA.Proofs.TR26.isotropic_degree
#print axioms NLA.Proofs.TR26.isotropic_degree
example (d : ℕ) (hd : 2 ≤ d) : NLA.Statements.TR26.HasReducedDegree d (2*d)
    (NLA.Statements.TR26.IsotropicImage d) := NLA.Proofs.TR26.isotropic_degree d hd
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
