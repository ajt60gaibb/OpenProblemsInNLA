/- Author proof-term audit. Traversal organization reused from campaign reviews; this is not independent review. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.MI03.modulus_semantics,
    ``NLA.MI03.contraction_modulus,
    ``NLA.MI03.positive_decomposition,
    ``NLA.MI03.universal_upper_bound,
    ``NLA.MI03.root_of_unity_data,
    ``NLA.MI03.sharpness_witness,
    ``NLA.MI03.sharp_constant,
    ``NLA.MI03.odd_contraction_conjecture]
  let mut visited : List Name := []
  let mut allConstants : List Name := []
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if let some body := info.value? (allowOpaque := true) then
          let constants := body.getUsedConstants.toList
          allConstants := constants ++ allConstants
          let projectDeps := constants.filter (fun n =>
            n.toString.startsWith "NLA.MI03." ||
              n.toString.startsWith "_private.NLA.MI03.")
          logInfo m!"PROJECT_EDGE {name}: {projectDeps}"
          pending := projectDeps ++ pending
  unless pending.isEmpty do throwError "Dependency traversal did not finish"
  for required in [``CFC.abs_mul_abs,
      ``CFC.norm_abs,
      ``CFC.sqrt_unique,
      ``CFC.abs_of_nonneg,
      ``CStarAlgebra.norm_le_one_iff_of_nonneg,
      ``Commute.mul_nonneg,
      ``Complex.isPrimitiveRoot_exp,
      ``IsPrimitiveRoot.geom_sum_eq_zero,
      ``EuclideanSpace.norm_sq_eq,
      ``CStarRing.norm_self_mul_star,
      ``Matrix.l2_opNorm_toEuclideanCLM,
      ``IsLeast.csInf_eq,
      ``Matrix.PosSemidef.diag_nonneg,
      ``NLA.MI03.pairVariance_identity,
      ``NLA.MI03.pairVariance_posSemidef,
      ``NLA.MI03.shiftedSquare_posSemidef,
      ``NLA.MI03.universal_upper_bound_proved,
      ``NLA.MI03.witness_modulus,
      ``NLA.MI03.witness_norm,
      ``NLA.MI03.witness_sum,
      ``NLA.MI03.witness_modulus_sum,
      ``NLA.MI03.witness_difference,
      ``NLA.MI03.lower_bound_proved,
      ``NLA.MI03.sharp_constant_proved,
      ``NLA.MI03.odd_contraction_conjecture_proved] do
    unless allConstants.contains required do
      throwError "Missing actual mathematical dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  logInfo m!"PROJECT_DECLARATIONS: {visited.length}"

#check NLA.MI03.modulus_semantics
#check NLA.MI03.contraction_modulus
#check NLA.MI03.positive_decomposition
#check NLA.MI03.universal_upper_bound
#check NLA.MI03.root_of_unity_data
#check NLA.MI03.sharpness_witness
#check NLA.MI03.sharp_constant
#check NLA.MI03.odd_contraction_conjecture

set_option pp.proofs true in
#print NLA.MI03.matrixModulus

set_option pp.proofs true in
#print NLA.MI03.operatorNorm

set_option pp.proofs true in
#print NLA.MI03.AdmissibleConstant

set_option pp.proofs true in
#print NLA.MI03.admissibleConstants

set_option pp.proofs true in
#print NLA.MI03.sharpConstant

set_option pp.proofs true in
#print NLA.MI03.OddContractionConjecture

set_option pp.proofs true in
#print NLA.MI03.lower_bound_proved

set_option pp.proofs true in
#print NLA.MI03.sharp_constant_proved

set_option pp.proofs true in
#print NLA.MI03.odd_contraction_conjecture_proved
