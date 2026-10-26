import NLA.Statements.TR26
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.TR26
theorem isotropic_degree (d : ℕ) (hd : 2 ≤ d) :
    NLA.Statements.TR26.HasReducedDegree d (2*d)
      (NLA.Statements.TR26.IsotropicImage d) := by
  sorry
end NLA.Proofs.TR26
