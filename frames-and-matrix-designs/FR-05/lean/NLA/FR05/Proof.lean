/- The unconditional FR-05 result, Propositions 3.1 and 3.2, and their prerequisites. -/

import NLA.FR05.Geometry.RankTwo
import NLA.FR05.FinalAssembly

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

/-- Existential form of the all-dimension exact ambiguity checkpoint. -/
theorem explicit_noninjective_frame_proved (d : ℕ) (hd : 2 ≤ d) :
    ∃ A : Frame (4 * d - 5) d, ¬ PhaseRetrievalInjective A := by
  refine ⟨flatFrame (4 * d - 5) d, ?_⟩
  exact flatFrame_not_phaseRetrievalInjective d hd

end NLA.FR05
