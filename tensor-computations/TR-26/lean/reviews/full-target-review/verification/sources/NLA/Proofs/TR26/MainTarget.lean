import NLA.Proofs.TR26.NonisotropicDegree
import NLA.Proofs.TR26.IsotropicDegree

/-! The unchanged all-order TR-26 target, retaining both exact projections
and all original matrix and full-incidence-ideal definitions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26

theorem target : NLA.Statements.TR26.Target := by
  intro d hd
  exact ⟨nonisotropic_degree d hd,isotropic_degree d hd⟩

#assert_trust kernel target
#print axioms target
end NLA.Proofs.TR26
