import Definitions

set_option autoImplicit false

namespace IE21

theorem l2Sq_zero (n : ℕ) : l2Sq (fun _ : Fin n => (0 : ℝ)) = 0 := by
  simp [l2Sq]

theorem rowEnergy_empty {m n : ℕ} (A : Matrix m n) (x : Fin n → ℝ) :
    rowEnergy A ∅ x = 0 := by
  simp [rowEnergy]

#print axioms l2Sq_zero
#print axioms rowEnergy_empty

end IE21
