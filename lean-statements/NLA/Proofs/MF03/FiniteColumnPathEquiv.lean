import NLA.Proofs.MF03.FiniteColumnPathLeftInverse
import NLA.Proofs.MF03.FiniteColumnPathRightInverse

/-!
The exact finite MF-03 valid paths and original advance-label column
systems are equivalent, with literal inverse maps and fixed endpoints.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Exact all-order equivalence between literal valid paths and the
finite column sets of their actual zero-based factor labels. -/
def finiteColumnPathEquiv {N m j : ℕ} (hj : j ≤ m) :
    FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m) ≃
      FiniteColumnSystem N m j where
  toFun := finitePathToColumnSystem N m j hj
  invFun := finiteColumnSystemToPath hj
  left_inv := finiteColumnPath_rightInverse hj
  right_inv := finiteColumnPath_leftInverse hj

#assert_trust kernel finiteColumnPathEquiv
#print axioms finiteColumnPathEquiv

end NLA.Proofs.MF03
