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
import NLA.IE23.Minimizers
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

/-- The supremum really is a finite nonnegative induced norm on every input
in the canonical domain, with no assumed boundedness or denominator premise. -/
theorem inducedNorm_semantics_proved {m n : ℕ} (hm : 1 ≤ m) (p : ℝ) (hp : 2 < p)
    (X : Mat n m) :
    (∀ y : Vec m, y ≠ 0 → 0 < lpNorm p y) ∧
    (ratioSet p X).Nonempty ∧ BddAbove (ratioSet p X) ∧
    IsLUB (ratioSet p X) (inducedNorm p X) ∧ 0 ≤ inducedNorm p X ∧
    (∀ y : Vec m, euclideanNorm (X.mulVec y) ≤ inducedNorm p X * lpNorm p y) := by
  have hp0 : 0 < p := by linarith
  exact ⟨fun _ hy => lpNorm_pos hp0 hy, ratioSet_nonempty hm p X,
    ratioSet_bddAbove hp0 X,
    isLUB_csSup (ratioSet_nonempty hm p X) (ratioSet_bddAbove hp0 X),
    inducedNorm_nonneg hm hp0 X, mulVec_le_inducedNorm hp0 X⟩

/-- Full-row-rank, actual inverse, actual Moore-Penrose identity, both right
inverse equations, distinctness, and both Gram matrices. -/
theorem witness_matrix_identities_proved :
    FullRowRank witnessA ∧
    witnessA * witnessA.conjTranspose = witnessGram ∧
    IsUnit witnessGram ∧ witnessGram⁻¹ = witnessGramInv ∧
    moorePenrose witnessA = witnessB ∧
    IsRightInverse witnessA witnessB ∧ IsRightInverse witnessA witnessX ∧
    witnessB ≠ witnessX ∧
    witnessB.conjTranspose * witnessB = witnessGramInv ∧
    witnessX.conjTranspose * witnessX = 1 := by
  exact ⟨witness_fullRowRank, witness_gram, witness_gram_isUnit,
    witness_gram_inverse, witness_moorePenrose, witness_B_rightInverse,
    witness_X_rightInverse, witness_B_ne_X, witness_B_gram, witness_X_gram⟩

/-- The exact fourth-root constant and the universal complex-vector bound.
All statements concern the true norms, not substituted power surrogates. -/
theorem fourth_power_norm_control_proved :
    2 < (4 : ℝ) ∧ 0 < witnessNorm ∧
    witnessNorm ^ (2 : ℕ) = Real.sqrt 2 ∧ witnessNorm ^ (4 : ℕ) = 2 ∧
    witnessNorm = (2 : ℝ) ^ ((1 / 2 : ℝ) - 1 / 4) ∧
    (∀ y : Vec 2,
      euclideanNorm y ^ (2 : ℕ) = ∑ i, Complex.normSq (y i)) ∧
    (∀ y : Vec 2,
      lpNorm 4 y ^ (4 : ℕ) = ∑ i, ‖y i‖ ^ (4 : ℕ)) ∧
    (∀ y : Vec 2, euclideanNorm y ≤ witnessNorm * lpNorm 4 y) := by
  exact ⟨by norm_num, witnessNorm_pos, witnessNorm_sq, witnessNorm_pow_four,
    witnessNorm_rpow, euclideanNorm_sq_normSq, lpNorm_fourth_power,
    euclideanNorm_le_four_norm⟩

/-- All complex input vectors, and all complex right inverses at the norming
vector, are covered by exact action identities. -/
theorem witness_action_identities_proved :
    (∀ y : Vec 2,
      euclideanNorm (witnessB.mulVec y) ^ (2 : ℕ) +
        Complex.normSq (y 0 + y 1) / 3 = euclideanNorm y ^ (2 : ℕ)) ∧
    (∀ y : Vec 2, euclideanNorm (witnessX.mulVec y) = euclideanNorm y) ∧
    (∀ Y : Mat 3 2, IsRightInverse witnessA Y →
      euclideanNorm (Y.mulVec normingVector) ^ (2 : ℕ) =
        2 + 3 * Complex.normSq ((Y.mulVec normingVector) 0)) := by
  exact ⟨witnessB_norm_identity, witnessX_norm_identity, competitor_norm_identity⟩

/-- The proposed upper bound is actually attained by a nonzero complex vector. -/
theorem witness_attainment_proved :
    normingVector ≠ 0 ∧ lpNorm 4 normingVector = witnessNorm ∧
    euclideanNorm (witnessB.mulVec normingVector) = Real.sqrt 2 ∧
    euclideanNorm (witnessX.mulVec normingVector) = Real.sqrt 2 ∧
    euclideanNorm (witnessB.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm ∧
    euclideanNorm (witnessX.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm := by
  exact ⟨normingVector_ne_zero, normingVector_lpNorm, witnessB_norming_norm,
    witnessX_norming_norm, witnessB_norming_ratio, witnessX_norming_ratio⟩

/-- These are equalities for the actual suprema over every nonzero vector. -/
theorem witness_norms_proved :
    inducedNorm 4 witnessB = witnessNorm ∧ inducedNorm 4 witnessX = witnessNorm := by
  exact ⟨witnessB_inducedNorm, witnessX_inducedNorm⟩

/-- Both distinct inverses are global minimizers among every admissible
complex competitor, and the minimum is attained with the stated exact value. -/
theorem witness_global_minimizers_proved :
    IsNormMinimizer witnessA 4 witnessB ∧ IsNormMinimizer witnessA 4 witnessX ∧
    IsLeast (rightInverseNorms witnessA 4) witnessNorm := by
  exact ⟨witnessB_global_minimizer, witnessX_global_minimizer, witness_minimum⟩

/-- Complete negative answer to the retained all-dimension/all-p conjecture. -/
theorem not_rightInverseUniqueConjecture_proved : ¬ RightInverseUniqueConjecture := by
  exact full_conjecture_negation

#assert_trust kernel inducedNorm_semantics_proved
#print axioms inducedNorm_semantics_proved
#assert_trust kernel witness_matrix_identities_proved
#print axioms witness_matrix_identities_proved
#assert_trust kernel fourth_power_norm_control_proved
#print axioms fourth_power_norm_control_proved
#assert_trust kernel witness_action_identities_proved
#print axioms witness_action_identities_proved
#assert_trust kernel witness_attainment_proved
#print axioms witness_attainment_proved
#assert_trust kernel witness_norms_proved
#print axioms witness_norms_proved
#assert_trust kernel witness_global_minimizers_proved
#print axioms witness_global_minimizers_proved
#assert_trust kernel not_rightInverseUniqueConjecture_proved
#print axioms not_rightInverseUniqueConjecture_proved

end NLA.IE23
