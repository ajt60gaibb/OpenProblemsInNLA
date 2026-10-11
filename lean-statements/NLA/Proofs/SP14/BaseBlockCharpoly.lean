import NLA.Statements.SP14

/-!
The characteristic polynomial of the unit lower-bidiagonal block arising
from the SP-14 base symbol. Identifying it with the product of the actual
even/odd Toeplitz blocks remains a separate proof obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix

namespace NLA.Proofs.SP14

/-- The finite unit lower-bidiagonal matrix predicted for `C * B` after
reordering the odd Toeplitz section by parity. -/
def baseBlock (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  fun i j => if i.val = j.val then 1 else if i.val = j.val + 1 then 1 else 0

/-- This algebraic block has all characteristic roots at one, with full
algebraic multiplicity `m`, including the empty `m=0` case. -/
theorem baseBlock_charpoly (m : ℕ) :
    (baseBlock m).charpoly = (Polynomial.X - 1) ^ m := by
  have ht : (baseBlock m)ᵀ.IsUpperTriangular := by
    intro i j hij
    change j.val < i.val at hij
    have hdiag : j.val ≠ i.val := by omega
    have hsub : j.val ≠ i.val + 1 := by omega
    simp [baseBlock, hdiag, hsub]
  calc
    (baseBlock m).charpoly = (baseBlock m)ᵀ.charpoly :=
      (Matrix.charpoly_transpose (baseBlock m)).symm
    _ = ∏ i : Fin m, (Polynomial.X - Polynomial.C ((baseBlock m)ᵀ i i)) :=
      Matrix.charpoly_of_isUpperTriangular _ ht
    _ = (Polynomial.X - 1) ^ m := by simp [baseBlock]

#assert_trust kernel baseBlock_charpoly
#print axioms baseBlock_charpoly

end NLA.Proofs.SP14
