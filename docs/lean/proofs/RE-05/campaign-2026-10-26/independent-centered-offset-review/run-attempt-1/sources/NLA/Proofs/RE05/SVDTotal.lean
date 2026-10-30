import NLA.Statements.RE05
import NLA.Proofs.TR04.SVDTotal

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.NonadaptiveMatrixQuery

/-- The actual shared primitive always chooses a valid full rectangular SVD,
including zero dimensions and rank-deficient inputs. The affirmative existence
fact is reused from the independently reviewed TR04 kernel proof. -/
theorem svd_total : SVDTotal := by
  intro a b B
  obtain ⟨U, sigma, V, h⟩ := NLA.Proofs.TR04.SVD.exists_validSVD B
  have hex : ∃ R : SVDResult a b, ValidSVDResult B R := ⟨⟨U, sigma, V⟩, h⟩
  unfold exactSVD
  rw [dif_pos hex]
  exact Classical.choose_spec hex

#assert_trust kernel svd_total
#print axioms svd_total
end NLA.Proofs.RE05
