/-
  MI20: Machine-Checked Formalization of Subquadratic Lee Constants (Open Problem MI-20)
  ======================================================================================
  Author:      Marcio Díaz
  Affiliation: Space Research AI (https://spaceresearch.ai, marcio.diaz@gmail.com)

  Full Lean 4 + Mathlib formalization covering:
    - Definitions & Schatten-p norm / matrix modulus infrastructure
    - Proposition 0 (Schatten-p subgradient bound), Lemma 1 (universal rank deficiency),
      Lemma 3 (polar optimality)
    - Existence of finite-dimensional maximizers & zero-padding monotonicity
    - Lemma 2 (full-rank sum via isometric left-rotation) & Same-Dimension Lemma 2
    - Lemma 4(a) (Sherman–Morrison rank-one Schatten-p smoothness), Lemma 4(b) (kernel lifting),
      Proposition 5 (superquadratic obstruction), Theorem 1 (strict infinite-dimensional hierarchy
      and non-existence of finite-dimensional extremizers)
    - Theorem 3 (universal 2×2 collapse and exact closed form at p = 3/2) &
      Theorem 4 (end-to-end pure-integer operator-monotone Sylvester certificate at p = 3/2)
    - Theorem 5 (exact PSD-splitting & POVM reformulation for 1 < p < 2)
    - Theorem 6 (Hadamard three-lines log-convexity & dimension-free p = 2 upper bound)

  Zero `sorry`, zero custom axioms (only Lean's standard [propext, Classical.choice, Quot.sound]).
-/

import MI20.Definitions
import MI20.SpectralBasics
import MI20.Prop0_And_Lemmas13
import MI20.ExistenceAndPadding
import MI20.Lemma2_LeftRotation
import MI20.Lemma4_And_Theorem1
import MI20.Theorem3_And_Theorem4
import MI20.Theorem5_PSDReduction
import MI20.Theorem6_LogConvexity
import MI20.Theorem9_10_CommutatorAndQuadraticBound
import MI20.Theorem10B_SharpUniversalAndSuperexp
