import NLA.Computation.NonadaptiveMatrixQuery
import NLA.Proofs.TR04.SVDTotal

/-! The SVD existence construction is reused byte for byte from the separately
reviewed TR-04 source. This wrapper proves validity of the actual choice made by
the unchanged RE-06 machine, including empty rectangular dimensions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.RE06
open NLA.Computation.NonadaptiveMatrixQuery

theorem svd_total : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := by
  intro a b B
  obtain ⟨U, sigma, V, h⟩ := NLA.Proofs.TR04.SVD.exists_validSVD B
  have hex : ∃ R : SVDResult a b, ValidSVDResult B R := ⟨⟨U, sigma, V⟩, h⟩
  unfold exactSVD
  rw [dif_pos hex]
  exact Classical.choose_spec hex

#assert_trust kernel svd_total
#print axioms svd_total
end NLA.Proofs.RE06
