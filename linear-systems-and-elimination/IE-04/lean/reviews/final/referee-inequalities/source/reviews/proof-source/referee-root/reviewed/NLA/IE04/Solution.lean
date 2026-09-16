/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

All 21 independent frozen obligations for the complete IE-04 resolution.
Challenge is never imported. Compilation and Comparator acceptance must be
established on Linux before this source is described as verified.
-/
import NLA.IE04.Final
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem entryMax_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, |A i j| ≤ entryMax A) ∧
      ∃ i j, entryMax A = |A i j| := entryMax_semantics_proved hn A

theorem firstPath_semantics {n : ℕ} (A : Mat n) (hA : A.det ≠ 0) :
    FirstAvailablePath A (firstPath A) ∧
      (∀ k, trajectory A (firstPath A) k = firstTrajectory A k) ∧
      ∀ path, FirstAvailablePath A path → path = firstPath A :=
  firstPath_semantics_proved A hA

theorem firstPath_admissibleRule (n : ℕ) : AdmissibleRule (@firstPath n) :=
  firstPath_admissibleRule_proved n

theorem gaussianMatrix_probability (n : ℕ) : IsProbabilityMeasure (gaussianMatrix n) :=
  gaussianMatrix_probability_proved n

theorem exceedanceEvent_measurable {n : ℕ} (center : Mat n) (σ t : ℝ)
    (rule : Mat n → PivotPath n) (hrule : AdmissibleRule rule) :
    MeasurableSet (exceedanceEvent center σ t rule) :=
  exceedanceEvent_measurable_proved center σ t rule hrule

#assert_trust kernel entryMax_semantics
#print axioms entryMax_semantics
#assert_trust kernel firstPath_semantics
#print axioms firstPath_semantics
#assert_trust kernel firstPath_admissibleRule
#print axioms firstPath_admissibleRule
#assert_trust kernel gaussianMatrix_probability
#print axioms gaussianMatrix_probability
#assert_trust kernel exceedanceEvent_measurable
#print axioms exceedanceEvent_measurable
#assert_trust kernel witness_trajectory
#print axioms witness_trajectory
#assert_trust kernel witness_strict_growth
#print axioms witness_strict_growth
#assert_trust kernel scalar_budgets
#print axioms scalar_budgets
#assert_trust kernel quotient_bounds
#print axioms quotient_bounds
#assert_trust kernel scalar_schur_error
#print axioms scalar_schur_error
#assert_trust kernel full_box_robust
#print axioms full_box_robust
#assert_trust kernel growth_on_box
#print axioms growth_on_box
#assert_trust kernel standard_normal_density_lower
#print axioms standard_normal_density_lower
#assert_trust kernel gaussian_interval_lower
#print axioms gaussian_interval_lower
#assert_trust kernel gaussian_box_product
#print axioms gaussian_box_product
#assert_trust kernel gaussian_box_probability
#print axioms gaussian_box_probability
#assert_trust kernel gaussian_box_in_actual_event
#print axioms gaussian_box_in_actual_event
#assert_trust kernel gepp_gaussian_tail_lower
#print axioms gepp_gaussian_tail_lower
#assert_trust kernel contradiction_dimension
#print axioms contradiction_dimension
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_uniformExponentialTail
#print axioms not_uniformExponentialTail

end NLA.IE04
