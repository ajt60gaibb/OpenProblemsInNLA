/- Independent final referee 1 inspection. Adapted from the disclosed author inspector, adding complete type/body edges and explicit project safety checks. No mathematical source is modified. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.RA08.not_concaveSpectralTransferConjecture]
  let mut visited : List Name := []
  let mut constants : List Name := []
  for _ in [:3000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      if !visited.contains name then
        visited := name :: visited
        let some info := env.find? name | throwError "Missing declaration: {name}"
        if info.isUnsafe then throwError "Unsafe reached project declaration: {name}"
        if info.isAxiom then throwError "Axiom in project namespace: {name}"
        if let some body := info.value? (allowOpaque := true) then
          let used := (body.getUsedConstants.toList ++ info.type.getUsedConstants.toList).eraseDups
          constants := used ++ constants
          let deps := used.filter (fun n => n.toString.startsWith "NLA.RA08." ||
            n.toString.startsWith "_private.NLA.RA08.")
          logInfo m!"PROJECT_EDGE {name}: {deps}"
          pending := deps ++ pending
  unless pending.isEmpty do throwError "Incomplete project dependency traversal"
  for required in [``NLA.RA08.orderedSpectral_exists_proved,
      ``Matrix.IsHermitian.spectral_theorem,
      ``Matrix.IsHermitian.eigenvalues₀_antitone,
      ``NLA.RA08.spectral_tail_norms_proved,
      ``NLA.RA08.selected_cfc_eq,
      ``cfcHom_eq_of_continuous_of_map_id,
      ``NLA.RA08.operator_rayleigh_bound_proved,
      ``Matrix.inner_toEuclideanCLM,
      ``Matrix.l2_opNorm_toEuclideanCLM,
      ``Matrix.l2_opNorm_diagonal,
      ``NLA.RA08.rectangular_kernel,
      ``LinearMap.finrank_le_finrank_of_injective,
      ``NLA.RA08.witness_fourth,
      ``NLA.RA08.approximation_fourth,
      ``NLA.RA08.witness_no_gap_eigenvector,
      ``Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues,
      ``Matrix.IsHermitian.mulVec_eigenvectorBasis,
      ``NLA.RA08.witness_projection_norm,
      ``NLA.RA08.minorant_scalar_proved,
      ``NLA.RA08.minorant_cfc,
      ``cfc_polynomial, ``cfc_mono,
      ``NLA.RA08.approximation_cfc,
      ``NLA.RA08.first_product, ``NLA.RA08.second_product, ``NLA.RA08.third_product,
      ``NLA.RA08.witness_K_squared_quadratic,
      ``NLA.RA08.witness_minorant_quadratic,
      ``NLA.RA08.witness_functional_rayleigh_lower,
      ``NLA.RA08.numerical_gap_positive_proved,
      ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
      ``NLA.RA08.counterexample_proved,
      ``NLA.RA08.not_concaveSpectralTransferConjecture_proved] do
    unless constants.contains required do
      throwError "Missing retained proof dependency: {required}"
    logInfo m!"RETAINED_DEPENDENCY: {required}"
  for forbidden in [``sorryAx, `Lean.ofReduceBool, `Lean.trustCompiler] do
    if constants.contains forbidden then throwError "Forbidden direct dependency: {forbidden}"
  for name in visited.filter (fun n => n.toString.startsWith
      "NLA.RA08.numerical_gap_positive_proved._proof_") do
    let some info := env.find? name | throwError "Missing certificate helper"
    logInfo m!"NUMERICAL_HELPER {name}: {info.type}"
  logInfo m!"INDEPENDENT_SAFE_PROJECT_DECLARATIONS_REACHABLE_FROM_FULL_NEGATION: {visited.length}"

#check NLA.RA08.orderedSpectral_exists
#check NLA.RA08.orderedSpectral_semantics
#check NLA.RA08.functionalCalculus_spectral
#check NLA.RA08.spectral_tail_norms
#check NLA.RA08.operator_rayleigh_bound
#check NLA.RA08.witness_data
#check NLA.RA08.witness_spectral_location
#check NLA.RA08.minorant_scalar
#check NLA.RA08.minorant_functional_calculus
#check NLA.RA08.witness_tail_data
#check NLA.RA08.witness_rational_certificate
#check NLA.RA08.numerical_gap_positive
#check NLA.RA08.counterexample
#check NLA.RA08.not_concaveSpectralTransferConjecture

set_option pp.all true in
#print NLA.RA08.ConcaveSpectralTransferConjecture
set_option pp.all true in
#print NLA.RA08.OrderedSpectralData
set_option pp.all true in
#print NLA.RA08.AdmissibleFunction
set_option pp.all true in
#print NLA.RA08.spectralNorm
set_option pp.all true in
#print NLA.RA08.functionalCalculus
set_option pp.all true in
#print NLA.RA08.truncation
set_option pp.all true in
#print NLA.RA08.functionTruncation
set_option pp.proofs true in
#print NLA.RA08.numerical_gap_positive_proved
set_option pp.proofs true in
#print NLA.RA08.counterexample_proved
set_option pp.proofs true in
#print NLA.RA08.not_concaveSpectralTransferConjecture_proved

set_option pp.proofs true in
#print NLA.RA08.numerical_gap_positive_proved._proof_1_7
#assert_trust kernel NLA.RA08.numerical_gap_positive_proved._proof_1_7
#print axioms NLA.RA08.numerical_gap_positive_proved._proof_1_7
#assert_trust kernel NLA.RA08.not_concaveSpectralTransferConjecture
#print axioms NLA.RA08.not_concaveSpectralTransferConjecture
