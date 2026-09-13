/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Complete IE-23 formalization of Matthew J. Colbrook's resolution, retaining
Dokmanić–Gribonval's attribution for the example. George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
LeanCert performs an explicit kernel trust audit of this pure exact proof;
no interval computation or external numerical certificate is needed.
-/
import NLA.IE23.Proof

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

/-- The supremum really is a finite nonnegative induced norm on every input
in the canonical domain, with no assumed boundedness or denominator premise. -/
theorem inducedNorm_semantics {m n : ℕ} (hm : 1 ≤ m) (p : ℝ) (hp : 2 < p)
    (X : Mat n m) :
    (∀ y : Vec m, y ≠ 0 → 0 < lpNorm p y) ∧
    (ratioSet p X).Nonempty ∧ BddAbove (ratioSet p X) ∧
    IsLUB (ratioSet p X) (inducedNorm p X) ∧ 0 ≤ inducedNorm p X ∧
    (∀ y : Vec m, euclideanNorm (X.mulVec y) ≤ inducedNorm p X * lpNorm p y) := by
  exact inducedNorm_semantics_proved hm p hp X

/-- Full-row-rank, actual inverse, actual Moore-Penrose identity, both right
inverse equations, distinctness, and both Gram matrices. -/
theorem witness_matrix_identities :
    FullRowRank witnessA ∧
    witnessA * witnessA.conjTranspose = witnessGram ∧
    IsUnit witnessGram ∧ witnessGram⁻¹ = witnessGramInv ∧
    moorePenrose witnessA = witnessB ∧
    IsRightInverse witnessA witnessB ∧ IsRightInverse witnessA witnessX ∧
    witnessB ≠ witnessX ∧
    witnessB.conjTranspose * witnessB = witnessGramInv ∧
    witnessX.conjTranspose * witnessX = 1 := by
  exact witness_matrix_identities_proved

/-- The exact fourth-root constant and the universal complex-vector bound.
All statements concern the true norms, not substituted power surrogates. -/
theorem fourth_power_norm_control :
    2 < (4 : ℝ) ∧ 0 < witnessNorm ∧
    witnessNorm ^ (2 : ℕ) = Real.sqrt 2 ∧ witnessNorm ^ (4 : ℕ) = 2 ∧
    witnessNorm = (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / 4) ∧
    (∀ y : Vec 2,
      euclideanNorm y ^ (2 : ℕ) = ∑ i, Complex.normSq (y i)) ∧
    (∀ y : Vec 2,
      lpNorm 4 y ^ (4 : ℕ) = ∑ i, ‖y i‖ ^ (4 : ℕ)) ∧
    (∀ y : Vec 2, euclideanNorm y ≤ witnessNorm * lpNorm 4 y) := by
  exact fourth_power_norm_control_proved

/-- All complex input vectors, and all complex right inverses at the norming
vector, are covered by exact action identities. -/
theorem witness_action_identities :
    (∀ y : Vec 2,
      euclideanNorm (witnessB.mulVec y) ^ (2 : ℕ) +
        Complex.normSq (y 0 + y 1) / 3 = euclideanNorm y ^ (2 : ℕ)) ∧
    (∀ y : Vec 2, euclideanNorm (witnessX.mulVec y) = euclideanNorm y) ∧
    (∀ Y : Mat 3 2, IsRightInverse witnessA Y →
      euclideanNorm (Y.mulVec normingVector) ^ (2 : ℕ) =
        2 + 3 * Complex.normSq ((Y.mulVec normingVector) 0)) := by
  exact witness_action_identities_proved

/-- The proposed upper bound is actually attained by a nonzero complex vector. -/
theorem witness_attainment :
    normingVector ≠ 0 ∧ lpNorm 4 normingVector = witnessNorm ∧
    euclideanNorm (witnessB.mulVec normingVector) = Real.sqrt 2 ∧
    euclideanNorm (witnessX.mulVec normingVector) = Real.sqrt 2 ∧
    euclideanNorm (witnessB.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm ∧
    euclideanNorm (witnessX.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm := by
  exact witness_attainment_proved

/-- These are equalities for the actual suprema over every nonzero vector. -/
theorem witness_norms :
    inducedNorm 4 witnessB = witnessNorm ∧ inducedNorm 4 witnessX = witnessNorm := by
  exact witness_norms_proved

/-- Both distinct inverses are global minimizers among every admissible
complex competitor, and the minimum is attained with the stated exact value. -/
theorem witness_global_minimizers :
    IsNormMinimizer witnessA 4 witnessB ∧ IsNormMinimizer witnessA 4 witnessX ∧
    IsLeast (rightInverseNorms witnessA 4) witnessNorm := by
  exact witness_global_minimizers_proved

/-- Complete negative answer to the retained all-dimension/all-p conjecture. -/
theorem not_rightInverseUniqueConjecture : ¬ RightInverseUniqueConjecture := by
  exact not_rightInverseUniqueConjecture_proved

#assert_trust kernel inducedNorm_semantics
#print axioms inducedNorm_semantics
#assert_trust kernel witness_matrix_identities
#print axioms witness_matrix_identities
#assert_trust kernel fourth_power_norm_control
#print axioms fourth_power_norm_control
#assert_trust kernel witness_action_identities
#print axioms witness_action_identities
#assert_trust kernel witness_attainment
#print axioms witness_attainment
#assert_trust kernel witness_norms
#print axioms witness_norms
#assert_trust kernel witness_global_minimizers
#print axioms witness_global_minimizers
#assert_trust kernel not_rightInverseUniqueConjecture
#print axioms not_rightInverseUniqueConjecture

end NLA.IE23
