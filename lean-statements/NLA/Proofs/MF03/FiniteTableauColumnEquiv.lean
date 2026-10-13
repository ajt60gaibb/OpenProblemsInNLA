import NLA.Proofs.MF03.FiniteColumnUniformInverse

/-!
The exact bounded augmented tableaux and exact sentinel-free column
systems are mutually inverse, for every `N,m,j` with `j≤m`.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- Exact tableau/column-system bijection on the original MF-03 shape. -/
noncomputable def finiteTableauColumnEquiv (N m j : ℕ) (hj : j ≤ m) :
    FiniteColumnSystem N m j ≃
      FiniteTableau (finiteAugShape m j) N where
  toFun := fun D => finiteColumnSystemToTableau D hj
  invFun := fun T => finiteTableauToColumnSystem hj T
  left_inv := finiteColumnSystem_roundTrip hj
  right_inv := finiteTableau_roundTrip hj

#assert_trust kernel finiteTableauColumnEquiv
#print axioms finiteTableauColumnEquiv

end NLA.Proofs.MF03
