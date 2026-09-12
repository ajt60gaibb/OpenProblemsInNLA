/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Attained suprema and global minimality for Colbrook's IE-23 counterexample.
The comparison covers every complex right inverse, not a proposed subclass.
The underlying matrix retains Dokmanić–Gribonval's attribution. AI-assisted
formalization, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE23.Actions

set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
namespace NLA.IE23

lemma witnessB_norm_le (y : Vec 2) :
    euclideanNorm (witnessB.mulVec y) ≤ euclideanNorm y := by
  apply (sq_le_sq₀ (euclideanNorm_nonneg _) (euclideanNorm_nonneg _)).mp
  have h := witnessB_norm_identity y
  have hn := Complex.normSq_nonneg (y 0 + y 1)
  linarith

lemma witnessB_norming_ratio :
    euclideanNorm (witnessB.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm := by
  rw [witnessB_norming_norm, normingVector_lpNorm]
  exact sqrt_two_div_witnessNorm

lemma witnessX_norming_ratio :
    euclideanNorm (witnessX.mulVec normingVector) / lpNorm 4 normingVector = witnessNorm := by
  rw [witnessX_norming_norm, normingVector_lpNorm]
  exact sqrt_two_div_witnessNorm

lemma witnessB_inducedNorm : inducedNorm 4 witnessB = witnessNorm := by
  apply le_antisymm
  · apply inducedNorm_le_of_bound (by decide : 1 ≤ 2) (by norm_num : (0 : ℝ) < 4)
    intro y
    exact (witnessB_norm_le y).trans (euclideanNorm_le_four_norm y)
  · rw [← witnessB_norming_ratio]
    exact ratio_le_inducedNorm (by norm_num) witnessB normingVector_ne_zero

lemma witnessX_inducedNorm : inducedNorm 4 witnessX = witnessNorm := by
  apply le_antisymm
  · apply inducedNorm_le_of_bound (by decide : 1 ≤ 2) (by norm_num : (0 : ℝ) < 4)
    intro y
    rw [witnessX_norm_identity]
    exact euclideanNorm_le_four_norm y
  · rw [← witnessX_norming_ratio]
    exact ratio_le_inducedNorm (by norm_num) witnessX normingVector_ne_zero

lemma competitor_inducedNorm_lower (Y : Mat 3 2) (hY : IsRightInverse witnessA Y) :
    witnessNorm ≤ inducedNorm 4 Y := by
  have hn : Real.sqrt 2 ≤ euclideanNorm (Y.mulVec normingVector) := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (euclideanNorm_nonneg _)).mp
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), competitor_norm_identity Y hY]
    have h := Complex.normSq_nonneg ((Y.mulVec normingVector) 0)
    linarith
  calc
    witnessNorm = Real.sqrt 2 / witnessNorm := sqrt_two_div_witnessNorm.symm
    _ ≤ euclideanNorm (Y.mulVec normingVector) / witnessNorm :=
      div_le_div_of_nonneg_right hn witnessNorm_pos.le
    _ = euclideanNorm (Y.mulVec normingVector) / lpNorm 4 normingVector := by
      rw [normingVector_lpNorm]
    _ ≤ inducedNorm 4 Y := ratio_le_inducedNorm (by norm_num) Y normingVector_ne_zero

lemma witnessB_global_minimizer : IsNormMinimizer witnessA 4 witnessB := by
  refine ⟨witness_B_rightInverse, ?_⟩
  intro Y hY
  rw [witnessB_inducedNorm]
  exact competitor_inducedNorm_lower Y hY

lemma witnessX_global_minimizer : IsNormMinimizer witnessA 4 witnessX := by
  refine ⟨witness_X_rightInverse, ?_⟩
  intro Y hY
  rw [witnessX_inducedNorm]
  exact competitor_inducedNorm_lower Y hY

lemma witness_minimum : IsLeast (rightInverseNorms witnessA 4) witnessNorm := by
  refine ⟨⟨witnessB, witness_B_rightInverse, witnessB_inducedNorm.symm⟩, ?_⟩
  rintro c ⟨Y, hY, rfl⟩
  exact competitor_inducedNorm_lower Y hY

lemma full_conjecture_negation : ¬ RightInverseUniqueConjecture := by
  intro h
  have hx : witnessX ≠ moorePenrose witnessA := by
    rw [witness_moorePenrose]
    exact witness_B_ne_X.symm
  have hc := h 2 3 (by decide) (by decide) witnessA witness_fullRowRank
    4 (by norm_num) witnessX witness_X_rightInverse hx
  rw [witness_moorePenrose, witnessB_inducedNorm, witnessX_inducedNorm] at hc
  exact lt_irrefl witnessNorm hc

end NLA.IE23
