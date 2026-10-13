import NLA.Proofs.RA06.Final

/-! The complete frozen RA-06 negative target, proved in the copied source. -/
set_option autoImplicit false

namespace NLA.RA06

theorem target : NLA.Statements.RA06.Target := by
  exact NLA.Proofs.RA06.target

end NLA.RA06
