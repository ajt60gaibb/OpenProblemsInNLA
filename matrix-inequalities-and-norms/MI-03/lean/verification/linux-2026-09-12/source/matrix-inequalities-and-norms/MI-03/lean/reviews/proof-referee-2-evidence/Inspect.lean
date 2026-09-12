/- Independent final referee 2. Traverse the freshly rebuilt target bodies,
not an author-supplied dependency JSON. Generic traversal technique is shared
with the campaign's earlier independent reviews. No candidate proof is edited. -/
import Solution
import Lean.Util.FoldConsts

set_option leancert.trust "kernel"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.MI03.modulus_semantics,
    ``NLA.MI03.contraction_modulus, ``NLA.MI03.positive_decomposition,
    ``NLA.MI03.universal_upper_bound, ``NLA.MI03.root_of_unity_data,
    ``NLA.MI03.sharpness_witness, ``NLA.MI03.sharp_constant,
    ``NLA.MI03.odd_contraction_conjecture]
  let mut seen : List Name := []
  let mut used : List Name := []
  for _ in [:2000] do
    match pending with
    | [] => pure ()
    | declaration :: rest =>
      pending := rest
      unless seen.contains declaration do
        seen := declaration :: seen
        let some info := env.find? declaration
          | throwError "Missing actual declaration: {declaration}"
        let some value := info.value? (allowOpaque := true)
          | throwError "Project declaration has no actual body: {declaration}"
        let dependencies := value.getUsedConstants.toList
        used := dependencies ++ used
        let localDependencies := dependencies.filter fun n =>
          n.toString.startsWith "NLA.MI03." || n.toString.startsWith "_private.NLA.MI03."
        logInfo m!"INDEPENDENT_EDGE {declaration}: {localDependencies}"
        pending := localDependencies ++ pending
  unless pending.isEmpty do throwError "Actual proof traversal did not terminate"
  for required in [``CFC.abs_mul_abs, ``CFC.norm_abs, ``CFC.sqrt_unique,
      ``CFC.abs_of_nonneg, ``CStarAlgebra.norm_le_one_iff_of_nonneg,
      ``Commute.mul_nonneg, ``Complex.isPrimitiveRoot_exp,
      ``IsPrimitiveRoot.geom_sum_eq_zero, ``EuclideanSpace.norm_sq_eq,
      ``CStarRing.norm_self_mul_star, ``Matrix.l2_opNorm_toEuclideanCLM,
      ``IsLeast.csInf_eq, ``Matrix.PosSemidef.diag_nonneg,
      ``NLA.MI03.pairVariance_identity, ``NLA.MI03.pairVariance_posSemidef,
      ``NLA.MI03.shiftedSquare_posSemidef, ``NLA.MI03.universal_upper_bound_proved,
      ``NLA.MI03.witness_modulus, ``NLA.MI03.witness_norm,
      ``NLA.MI03.witness_sum, ``NLA.MI03.witness_modulus_sum,
      ``NLA.MI03.witness_difference, ``NLA.MI03.lower_bound_proved,
      ``NLA.MI03.sharp_constant_proved, ``NLA.MI03.odd_contraction_conjecture_proved,
      ``CFC.abs_nonneg, ``Matrix.posSemidef_conjTranspose_mul_self,
      ``Matrix.posSemidef_vecMulVec_self_star, ``Matrix.l2_opNorm_diagonal,
      ``NLA.MI03.witnessVector_norm, ``NLA.MI03.witness_reverse_gram] do
    unless used.contains required do throwError "Required dependency absent: {required}"
    logInfo m!"INDEPENDENT_RETAINED: {required}"
  logInfo m!"INDEPENDENT_PROJECT_DECLARATIONS: {seen.length}"

#check NLA.MI03.modulus_semantics
#check NLA.MI03.contraction_modulus
#check NLA.MI03.positive_decomposition
#check NLA.MI03.universal_upper_bound
#check NLA.MI03.root_of_unity_data
#check NLA.MI03.sharpness_witness
#check NLA.MI03.sharp_constant
#check NLA.MI03.odd_contraction_conjecture

set_option pp.explicit true in
#print NLA.MI03.operatorNorm
set_option pp.explicit true in
#print NLA.MI03.matrixModulus
#print NLA.MI03.AdmissibleConstant
#print NLA.MI03.admissibleConstants
#print NLA.MI03.sharpConstant
#print NLA.MI03.OddContractionConjecture

set_option pp.proofs true in
#print NLA.MI03.positive_decomposition_proved
set_option pp.proofs true in
#print NLA.MI03.witness_modulus
set_option pp.proofs true in
#print NLA.MI03.witness_norm
set_option pp.proofs true in
#print NLA.MI03.lower_bound_proved
set_option pp.proofs true in
#print NLA.MI03.sharp_constant_proved
set_option pp.proofs true in
#print NLA.MI03.odd_contraction_conjecture_proved
