import NLA.Proofs.TR26.NonisotropicAssembly
import NLA.Proofs.TR26.FiniteProjectiveDensity

/-! The exact reduced degree of the full nonisotropic projective closure. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR26
open NLA.Statements.TR26

theorem nonisotropic_degree (d : ℕ) (hd : 2 ≤ d) :
    HasReducedDegree d (6*(d-1)) (NonisotropicClosure d) :=
  nonisotropic_degree_of_fullImage_ideal_eq hd (nonisotropicImage_vanishingIdeal_eq_finite hd)

#assert_trust kernel nonisotropic_degree
#print axioms nonisotropic_degree
end NLA.Proofs.TR26
