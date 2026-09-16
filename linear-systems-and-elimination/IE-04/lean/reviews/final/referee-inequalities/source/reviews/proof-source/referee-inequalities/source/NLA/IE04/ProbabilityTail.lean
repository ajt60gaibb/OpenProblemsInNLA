/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The genuine Gaussian box is contained in the actual algorithmic tail event
for every measurable admissible rule. Both nonsingularity and growth come
from the full closed-box proof, not a distributional assumption.
-/
import NLA.IE04.GaussianBox
import NLA.IE04.Robustness
import NLA.IE04.Measurability
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory
noncomputable section
namespace NLA.IE04

theorem gaussianBox_smoothedInput {n : ℕ} (G : Mat n) (hG : G ∈ gaussianBox n) :
    InWitnessBox (smoothedInput (1 : Mat n) 1 G) := by
  change InWitnessBox ((1 : Mat n) + (1 : ℝ) • G)
  rw [one_smul]
  intro i j
  have h := hG i j
  change |(1 : Mat n) i j + G i j - witnessMatrix n i j| ≤ boxRadius n
  convert h using 1
  congr 1
  ring

theorem gaussian_box_in_actual_event {n : ℕ} (hn : 2 ≤ n)
    (rule : Mat n → PivotPath n) (hrule : AdmissibleRule rule) :
    gaussianBox n ⊆ exceedanceEvent (1 : Mat n) 1 (growthThreshold n) rule := by
  intro G hG
  let A := smoothedInput (1 : Mat n) 1 G
  have hbox : InWitnessBox A := gaussianBox_smoothedInput G hG
  have hdet := (full_box_robust hn A hbox).1
  have hpath := hrule.1 A hdet
  exact ⟨hdet, (growth_on_box hn A hbox (rule A) hpath).2.2⟩

theorem gepp_gaussian_tail_lower {n : ℕ} (hn : 2 ≤ n)
    (rule : Mat n → PivotPath n) (hrule : AdmissibleRule rule) :
    ENNReal.ofReal (1 / (2 : ℝ) ^ probabilityExponent n) ≤
      gaussianMatrix n (exceedanceEvent (1 : Mat n) 1 (growthThreshold n) rule) :=
  (gaussian_box_probability hn).trans
    (measure_mono (gaussian_box_in_actual_event hn rule hrule))

#assert_trust kernel gaussian_box_in_actual_event
#print axioms gaussian_box_in_actual_event
#assert_trust kernel gepp_gaussian_tail_lower
#print axioms gepp_gaussian_tail_lower

end NLA.IE04
