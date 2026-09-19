import NLA.PF03.Definitions
import LeanCert.Tactic

/-!
C11: check the fixed rational functional on the21actual generator products.
These are exact rational inequalities, with no sampled real input or interval
subdivision. The full cone proof will consume strict positivity.

Original mathematics and data: Sidney Holden, Flatiron Institute, Simons
Foundation. Formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology; Codex assistance.
-/

set_option autoImplicit false
open scoped BigOperators Matrix
noncomputable section
namespace NLA.PF03

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem positive_slice_certificate :
    positiveSlice = RawData.positiveSlice ∧
      ∀ i : Fin 7, ∀ j : Fin 3,
        0 < ∑ r : Fin 7, positiveSlice r * generator i j r := by
  constructor
  · funext r
    fin_cases r <;> norm_num [positiveSlice, RawData.positiveSlice]
  · intro i
    fin_cases i <;> decide +kernel

#print axioms positive_slice_certificate
#assert_trust kernel positive_slice_certificate

end NLA.PF03
