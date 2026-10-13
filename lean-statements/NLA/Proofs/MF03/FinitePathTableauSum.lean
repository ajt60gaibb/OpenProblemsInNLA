import NLA.Proofs.MF03.FinitePathTableauWeight

/-!
The original finite valid paths and bounded augmented tableaux are
equivalent, and their original weights have equal finite sums.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

/-- The literal path/tableau bijection: actual path advance-label columns
followed by the exact column-system/tableau equivalence. -/
noncomputable def finitePathTableauEquiv (N m j : ℕ) (hj : j ≤ m) :
    FiniteValidPath m N (finitePathStart m j hj) (finitePathEnd m) ≃
      FiniteTableau (finiteAugShape m j) N :=
  (finiteColumnPathEquiv hj).trans (finiteTableauColumnEquiv N m j hj)

/-- The original finite path sum is exactly the original finite
augmented-tableau sum, in every order including empty domains. -/
theorem finiteValidPathSum_eq_augTableauSum (N m j : ℕ) (hj : j ≤ m) :
    finiteValidPathSum m N (finitePathStart m j hj) (finitePathEnd m) =
      finiteAugTableauSum N m j := by
  classical
  unfold finiteValidPathSum finiteAugTableauSum
  refine Fintype.sum_equiv (finitePathTableauEquiv N m j hj) _ _ ?_
  intro c
  exact finiteValidPathWeight_eq_tableauWeight hj c

#assert_trust kernel finitePathTableauEquiv
#assert_trust kernel finiteValidPathSum_eq_augTableauSum
#print axioms finiteValidPathSum_eq_augTableauSum

end NLA.Proofs.MF03
