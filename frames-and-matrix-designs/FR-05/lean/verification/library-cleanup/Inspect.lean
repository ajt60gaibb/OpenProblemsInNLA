import Solution

open scoped Topology

-- The original quantitative statement and limit are unchanged by the API refactor.
example : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
    NLA.FR05.phaseRetrievalProbability d ≤ C / d :=
  NLA.FR05.phaseRetrieval_injective_probability_le_inv

example : Filter.Tendsto NLA.FR05.phaseRetrievalProbability Filter.atTop (𝓝 0) :=
  NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero

#print axioms MeasureTheory.Measure.map_prod_eq_withDensity
#print axioms MeasureTheory.Measure.pi_withDensity_ofReal
#print axioms MeasureTheory.Measure.map_prod_eq_withDensity_ofReal
#print axioms MeasureTheory.Measure.map_prod_eq_withDensity_of_inv
#print axioms MeasureTheory.abs_setIntegral_le_sqrt_setIntegral_sq
#print axioms MeasureTheory.abs_setIntegral_le_sqrt_integral_sq
#print axioms NLA.FR05.phaseRetrievalInjective_iff_of_linearEquiv
#print axioms NLA.FR05.phaseRetrievalInjective_mul_diagonal
#print axioms NLA.FR05.measurePreserving_real_star_dotProduct
#print axioms Matrix.IsHermitian.det_one_add_smul_eq_prod
#print axioms NLA.FR05.standardComplexGaussianTail_map_splitSum
#print axioms NLA.FR05.gaussianMatrixProjection_law_eq_of_gram
#print axioms NLA.FR05.gaussianReal_abs_add_smallBall_uniform
#print axioms NLA.FR05.sourceOverlapLaw_eq_haarCorner
#print axioms NLA.FR05.volume_phaseCircle_preimage
#print axioms NLA.FR05.sourceUniformInterval_phase_preimage
#print axioms NLA.FR05.exists_row_mem_otherRowSpan_of_not_isUnit_det
#print axioms NLA.FR05.exists_unit_mem_otherRowSpan_orthogonal
#print axioms NLA.FR05.cone_integral_sq_le
#print axioms NLA.FR05.kernelEvenExp_factor_bound
#print axioms NLA.FR05.kernel_even_exp_remainder
#print axioms NLA.FR05.sourceEquation_midpoint_difference_identity
#print axioms NLA.FR05.sourceEquation_nonlinear_difference_le
#print axioms NLA.FR05.arccos_gap_sq_le
#print axioms NLA.FR05.arccos_gap_le_pi_sqrt
#print axioms NLA.FR05.volume_cosineBandPhaseSublevel_le
#print axioms NLA.FR05.affineTrig_cosine_normalForm
#print axioms NLA.FR05.norm_sq_le_squaredEuclideanNorm
#print axioms NLA.FR05.euclideanNorm_le_sqrt_card_mul_of_abs_le
#print axioms NLA.FR05.abs_plantedEquationLinear_sub_sourceRowJacobianForm_le_of_radial_tail
#print axioms NLA.FR05.proposition_3_1
#print axioms NLA.FR05.proposition_3_1_haar
#print axioms NLA.FR05.proposition_3_2
#print axioms NLA.FR05.source_haar_planted_frame_law_eq_likelihood
#print axioms NLA.FR05.source_reference_frame_law_eq_likelihood
#print axioms NLA.FR05.source_reference_injective_probability
#print axioms NLA.FR05.phaseRetrieval_probability_le_planted_add_sqrt
#print axioms NLA.FR05.phaseRetrieval_injective_probability_le_inv
#print axioms NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero

-- Follow proof terms, not just imports or occurrences in source text. This ensures
-- that every new substantive API lemma from these cleanup passes is actually
-- used by the original final theorem. Compatibility aliases are intentionally excluded.
open Lean in
run_cmd do
  let env ← getEnv
  let mut todo := [`NLA.FR05.phaseRetrieval_injective_probability_tendsto_zero]
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let name := todo.head!
    todo := todo.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      let deps := info.type.getUsedConstants ++
        (info.value? (allowOpaque := true)).toArray.flatMap (·.getUsedConstants)
      for dep in deps do
        if let some idx := env.getModuleIdxFor? dep then
          let mod := env.header.moduleNames[idx.toNat]!
          if (`NLA).isPrefixOf mod || mod == `Solution then
            todo := dep :: todo
  let candidates := #[
    `MeasureTheory.Measure.pi_withDensity_ofReal,
    `MeasureTheory.Measure.map_prod_eq_withDensity,
    `MeasureTheory.Measure.map_prod_eq_withDensity_ofReal,
    `MeasureTheory.Measure.map_prod_eq_withDensity_of_inv,
    `MeasureTheory.abs_setIntegral_le_sqrt_setIntegral_sq,
    `MeasureTheory.abs_setIntegral_le_sqrt_integral_sq,
    `NLA.FR05.GloballyPhased.map,
    `NLA.FR05.globallyPhased_linearEquiv_iff,
    `NLA.FR05.rowMagnitude_mul,
    `NLA.FR05.sameMeasurements_mul,
    `NLA.FR05.phaseRetrievalInjective_iff_of_linearEquiv,
    `NLA.FR05.phaseRetrievalInjective_mul_diagonal,
    `NLA.FR05.measurePreserving_real_star_dotProduct,
    `Matrix.IsHermitian.det_one_add_smul_eq_prod,
    `NLA.FR05.volume_phaseCircle_preimage,
    `NLA.FR05.sourceUniformInterval_phase_preimage,
    `NLA.FR05.kernelEvenExp_factor_bound,
    `NLA.FR05.sourceEquation_midpoint_difference_identity]
  for name in candidates do
    unless seen.contains name do throwError "Not used by the final proof: {name}"
  logInfo m!"All {candidates.size} new API lemmas occur in the final proof dependency closure."
