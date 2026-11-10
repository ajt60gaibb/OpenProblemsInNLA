import Definitions
import NLA.Proofs.IE22.Final

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace IE22

theorem l2Sq_zero (n : ℕ) : l2Sq (fun _ : Fin n => (0 : ℝ)) = 0 := by
  simp [l2Sq]

theorem rowEnergy_empty {m n : ℕ} (A : Matrix m n) (x : Fin n → ℝ) :
    rowEnergy A ∅ x = 0 := by
  simp [rowEnergy]

#print axioms l2Sq_zero
#print axioms rowEnergy_empty

end IE22

-- The exact three pre-reviewed endpoints are supplied by the imported proof.
#assert_trust kernel NLA.Proofs.IE22.uniform_squared_upper
#assert_trust kernel NLA.Proofs.IE22.near_sharp_unit_row_witness
#assert_trust kernel NLA.Proofs.IE22.target
#assert_trust kernel IE22.l2Sq_zero
#assert_trust kernel IE22.rowEnergy_empty
