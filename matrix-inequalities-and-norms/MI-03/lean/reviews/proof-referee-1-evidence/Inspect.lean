/- Independent MI-03 final referee 1 environment inspection.
Uses the campaign's generic FoldConsts traversal, with independently selected
mathematical dependencies and declaration-kind/safety checks. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := [``NLA.MI03.modulus_semantics, ``NLA.MI03.contraction_modulus,
    ``NLA.MI03.positive_decomposition, ``NLA.MI03.universal_upper_bound,
    ``NLA.MI03.root_of_unity_data, ``NLA.MI03.sharpness_witness,
    ``NLA.MI03.sharp_constant, ``NLA.MI03.odd_contraction_conjecture]
  for name in exports do
    let some (.thmInfo _) := env.find? name | throwError "Not an actual theorem: {name}"
  let mut queue := exports
  let mut visited : List Name := []
  let mut constants : List Name := []
  for _ in [:3000] do
    match queue with
    | [] => pure ()
    | name :: rest =>
      queue := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing project declaration: {name}"
        if info.isAxiom then throwError "Project axiom: {name}"
        if info.isUnsafe then throwError "Unsafe project declaration: {name}"
        let mut used := info.type.getUsedConstants.toList
        if let some body := info.value? (allowOpaque := true) then
          used := body.getUsedConstants.toList ++ used
        constants := used ++ constants
        let reached := used.filter (fun n => n.toString.startsWith "NLA.MI03." ||
          n.toString.startsWith "_private.NLA.MI03.")
        logInfo m!"CHECKED_PROJECT_EDGE {name}: {reached}"
        queue := reached ++ queue
  unless queue.isEmpty do throwError "Project dependency traversal limit exhausted"
  for required in [``CFC.abs_nonneg, ``CFC.abs_mul_abs, ``CFC.norm_abs,
      ``CFC.sqrt_unique, ``CFC.abs_of_nonneg,
      ``Matrix.l2_opNorm_toEuclideanCLM,
      ``CStarAlgebra.norm_le_one_iff_of_nonneg, ``Commute.mul_nonneg,
      ``Matrix.posSemidef_conjTranspose_mul_self,
      ``Matrix.posSemidef_vecMulVec_self_star,
      ``Complex.isPrimitiveRoot_exp, ``IsPrimitiveRoot.geom_sum_eq_zero,
      ``EuclideanSpace.norm_sq_eq, ``CStarRing.norm_self_mul_star,
      ``Matrix.PosSemidef.diag_nonneg, ``IsLeast.csInf_eq,
      ``NLA.MI03.modulus_square, ``NLA.MI03.contraction_modulus_proved,
      ``NLA.MI03.pairVariance_identity, ``NLA.MI03.shiftedSquare_posSemidef,
      ``NLA.MI03.positive_decomposition_proved,
      ``NLA.MI03.universal_upper_bound_proved,
      ``NLA.MI03.witnessVector_inner, ``NLA.MI03.witnessVector_norm,
      ``NLA.MI03.witness_gram, ``NLA.MI03.witnessModulus_idempotent,
      ``NLA.MI03.witness_modulus, ``NLA.MI03.witness_reverse_gram,
      ``NLA.MI03.witness_norm, ``NLA.MI03.witness_sum,
      ``NLA.MI03.witness_modulus_sum, ``NLA.MI03.witness_sum_posSemidef,
      ``NLA.MI03.witness_difference, ``NLA.MI03.lower_bound_proved,
      ``NLA.MI03.sharp_constant_proved] do
    unless constants.contains required do throwError "Missing actual dependency: {required}"
    logInfo m!"REQUIRED_DEPENDENCY_PRESENT {required}"
  logInfo m!"SAFE_PROJECT_DECLARATIONS_TRAVERSED {visited.length}"
  logInfo m!"PUBLIC_THEOREM_KINDS_VERIFIED {exports.length}"

#assert_trust kernel NLA.MI03.modulus_semantics
#print axioms NLA.MI03.modulus_semantics
#assert_trust kernel NLA.MI03.contraction_modulus
#print axioms NLA.MI03.contraction_modulus
#assert_trust kernel NLA.MI03.positive_decomposition
#print axioms NLA.MI03.positive_decomposition
#assert_trust kernel NLA.MI03.universal_upper_bound
#print axioms NLA.MI03.universal_upper_bound
#assert_trust kernel NLA.MI03.root_of_unity_data
#print axioms NLA.MI03.root_of_unity_data
#assert_trust kernel NLA.MI03.sharpness_witness
#print axioms NLA.MI03.sharpness_witness
#assert_trust kernel NLA.MI03.sharp_constant
#print axioms NLA.MI03.sharp_constant
#assert_trust kernel NLA.MI03.odd_contraction_conjecture
#print axioms NLA.MI03.odd_contraction_conjecture
#assert_trust kernel NLA.MI03.modulus_square
#print axioms NLA.MI03.modulus_square
#assert_trust kernel NLA.MI03.witness_modulus
#print axioms NLA.MI03.witness_modulus
#assert_trust kernel NLA.MI03.lower_bound_proved
#print axioms NLA.MI03.lower_bound_proved
#assert_trust kernel NLA.MI03.sharp_constant_proved
#print axioms NLA.MI03.sharp_constant_proved

#check @CFC.sqrt_unique
#check @CFC.abs_of_nonneg
#check @CStarAlgebra.norm_le_one_iff_of_nonneg
#check @Commute.mul_nonneg
#check @Complex.isPrimitiveRoot_exp
#check @IsPrimitiveRoot.geom_sum_eq_zero
#check @IsLeast.csInf_eq
#check @NLA.MI03.modulus_semantics
#check @NLA.MI03.contraction_modulus
#check @NLA.MI03.positive_decomposition
#check @NLA.MI03.universal_upper_bound
#check @NLA.MI03.root_of_unity_data
#check @NLA.MI03.sharpness_witness
#check @NLA.MI03.sharp_constant
#check @NLA.MI03.odd_contraction_conjecture

set_option pp.explicit true in
#print NLA.MI03.matrixModulus
set_option pp.explicit true in
#print NLA.MI03.operatorNorm
#print NLA.MI03.AdmissibleConstant
#print NLA.MI03.admissibleConstants
#print NLA.MI03.sharpConstant
#print NLA.MI03.OddContractionConjecture
set_option pp.proofs true in
#print NLA.MI03.witness_modulus
set_option pp.proofs true in
#print NLA.MI03.lower_bound_proved
set_option pp.proofs true in
#print NLA.MI03.sharp_constant_proved
set_option pp.proofs true in
#print NLA.MI03.odd_contraction_conjecture_proved
