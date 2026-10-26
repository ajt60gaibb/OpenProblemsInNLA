import Solution
import Reviewed.TR26
set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command
elab "#package_theorem " target:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  match ← liftCoreM <| getConstInfo name with
  | .thmInfo _ => pure ()
  | _ => throwError "package requires an actual theorem: {name}"
#package_theorem NLA.Proofs.TR26.nonisotropic_degree
#package_theorem NLA.Proofs.TR26.isotropic_degree
#package_theorem NLA.Proofs.TR26.target
#assert_trust kernel NLA.Proofs.TR26.nonisotropic_degree
#assert_trust kernel NLA.Proofs.TR26.isotropic_degree
#assert_trust kernel NLA.Proofs.TR26.target
#print axioms NLA.Proofs.TR26.nonisotropic_degree
#print axioms NLA.Proofs.TR26.isotropic_degree
#print axioms NLA.Proofs.TR26.target
example (d : ℕ) (hd : 2 ≤ d) :
    NLA.ReviewedStatements.TR26.HasReducedDegree d (6*(d-1))
      (NLA.ReviewedStatements.TR26.NonisotropicClosure d) :=
  NLA.Proofs.TR26.nonisotropic_degree d hd
example (d : ℕ) (hd : 2 ≤ d) :
    NLA.ReviewedStatements.TR26.HasReducedDegree d (2*d)
      (NLA.ReviewedStatements.TR26.IsotropicImage d) :=
  NLA.Proofs.TR26.isotropic_degree d hd
example : NLA.ReviewedStatements.TR26.Target := NLA.Proofs.TR26.target
example : NLA.Statements.TR26.Target = NLA.ReviewedStatements.TR26.Target := rfl
