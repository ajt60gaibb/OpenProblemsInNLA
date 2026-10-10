import NLA.Proofs.MF03.FinitePathTableauSum

/-!
The original finite Jacobi–Trudi augmented determinant equals the
original bounded augmented-tableau sum in every order. This identity
does not assert the eventual MF-03 tail bound or all-order Target.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Exact original finite augmented determinant/tableau identity, with
the original matrix order and the original cell weights. -/
theorem finiteCosineAugDet_eq_augTableauSum (N m j : ℕ) (hj : j ≤ m) :
    finiteCosineAugDet N m j = finiteAugTableauSum N m j :=
  (finiteCosineAugDet_eq_validPathSum N m j hj).trans
    (finiteValidPathSum_eq_augTableauSum N m j hj)

#assert_trust kernel finiteCosineAugDet_eq_augTableauSum
#print axioms finiteCosineAugDet_eq_augTableauSum

end NLA.Proofs.MF03
