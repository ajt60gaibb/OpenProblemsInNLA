import NLA.Proofs.MF03.FiniteTableauUniformCuts

/-!
Package the actual, sentinel-free advance labels extracted from an exact
finite augmented tableau. The resulting column system retains the exact
one-gap noncollision condition of the original path endpoints.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The exact inverse column-system data of a bounded augmented tableau. -/
noncomputable def finiteTableauToColumnSystem {N m j : ℕ}
    (hj : j ≤ m) (T : FiniteTableau (finiteAugShape m j) N) :
    FiniteColumnSystem N m j where
  labels := finiteTableauActualLabels T
  label_lt := by
    intro p k hk
    exact finiteTableauActualLabels_lt hj T p k hk
  card_eq := finiteTableauActualLabels_card hj T
  noncollision := by
    intro q hq p hp
    exact finiteTableauActualLabels_noncollision hj T q hq p hp

#assert_trust kernel finiteTableauToColumnSystem
#print axioms finiteTableauToColumnSystem

end NLA.Proofs.MF03
