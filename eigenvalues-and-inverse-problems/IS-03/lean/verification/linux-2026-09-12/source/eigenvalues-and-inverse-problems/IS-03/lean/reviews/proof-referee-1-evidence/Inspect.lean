/- Independent IS-03 final referee 1: inspect actual fresh proof values and types.
Authored by /root/leancert_examples, neither statement nor proof author.
The traversal pattern adapts this reviewer's IV-06/MI-03 inspections; every
IS-03 mathematical dependency and scope check is independently selected.
-/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut pending := [``NLA.IS03.nonnegative_power_trace,
    ``NLA.IS03.witness_admissible, ``NLA.IS03.witness_polynomials,
    ``NLA.IS03.trace_moment_certificate, ``NLA.IS03.negative_moment,
    ``NLA.IS03.counterexample, ``NLA.IS03.not_derivativeRealizabilityConjecture]
  let mut seen : List Name := []
  let mut used : List Name := []
  for _ in [:2500] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := name :: seen
        let some info := env.find? name | throwError "Missing project declaration: {name}"
        if info.isUnsafe || info.isPartial then
          throwError "Unsafe or partial project declaration: {name}"
        let some value := info.value? (allowOpaque := true)
          | throwError "Project declaration without a proof/definition body: {name}"
        let axs ← liftCoreM <| collectAxioms name
        for ax in axs do
          unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
            throwError "Forbidden transitive axiom at {name}: {ax}"
        let constants := info.type.getUsedConstants.toList ++ value.getUsedConstants.toList
        used := constants ++ used
        let localDeps := constants.filter fun n =>
          n.toString.startsWith "NLA.IS03." || n.toString.startsWith "_private.NLA.IS03."
        logInfo m!"REFEREE_SAFE_EDGE {name}: {localDeps}"
        pending := localDeps ++ pending
  unless pending.isEmpty do throwError "Incomplete project proof traversal"
  for required in [``Matrix.pow_apply_nonneg, ``Matrix.charpoly_reindex,
    ``Matrix.charpoly_fromBlocks_zero₁₂, ``Matrix.det_fin_three,
    ``Matrix.det_succ_row_zero, ``Polynomial.card_rootSet_eq_natDegree,
    ``Module.End.hasEigenvalue_iff_isRoot_charpoly,
    ``Module.End.HasEigenvalue.exists_hasEigenvector,
    ``Module.End.eigenvectors_linearIndependent',
    ``basisOfLinearIndependentOfCardEqFinrank',
    ``Module.End.HasEigenvector.pow_apply,
    ``Matrix.charpoly_map, ``Matrix.charpoly_toLin',
    ``Matrix.charpoly_diagonal, ``LinearMap.charpoly_toMatrix,
    ``Matrix.map_pow, ``Matrix.toLin'_pow, ``AddMonoidHom.map_trace,
    ``Matrix.trace_toLin'_eq, ``LinearMap.trace_eq_matrix_trace,
    ``Multiset.prod_X_sub_C_coeff, ``MvPolynomial.psum_eq_mul_esymm_sub_sum,
    ``LeanCert.Validity.verify_strict_upper_bound_dyadic_checked,
    ``NLA.IS03.derivativePolynomial_separable, ``NLA.IS03.complexRoots_card,
    ``NLA.IS03.exists_root_eigenbasis, ``NLA.IS03.root_product_and_trace,
    ``NLA.IS03.power_sums_of_derivative_product,
    ``NLA.IS03.numerical_negative_moment, ``NLA.IS03.negative_moment_proved,
    ``NLA.IS03.trace_moment_certificate_proved, ``NLA.IS03.counterexample_proved,
    ``NLA.IS03.not_derivativeRealizabilityConjecture_proved] do
    unless used.contains required do throwError "Material dependency absent: {required}"
    logInfo m!"REFEREE_RETAINED: {required}"
  logInfo m!"REFEREE_PROJECT_DECLARATIONS: {seen.length}"

#check NLA.IS03.nonnegative_power_trace
#check NLA.IS03.witness_admissible
#check NLA.IS03.witness_polynomials
#check NLA.IS03.trace_moment_certificate
#check NLA.IS03.negative_moment
#check NLA.IS03.counterexample
#check NLA.IS03.not_derivativeRealizabilityConjecture

set_option pp.all true in
#print NLA.IS03.DerivativeRealizabilityConjecture
set_option pp.all true in
#print NLA.IS03.trace_moment_certificate
set_option pp.all true in
#print NLA.IS03.exists_root_eigenbasis
set_option pp.all true in
#print NLA.IS03.ComplexRoots
set_option pp.proofs true in
#print NLA.IS03.derivativePolynomial_separable
set_option pp.proofs true in
#print NLA.IS03.root_product_and_trace
set_option pp.proofs true in
#print NLA.IS03.powerMoments_newton
set_option pp.proofs true in
#print NLA.IS03.numerical_negative_moment
set_option pp.proofs true in
#print NLA.IS03.trace_moment_certificate_proved
set_option pp.proofs true in
#print NLA.IS03.counterexample_proved
set_option pp.proofs true in
#print NLA.IS03.not_derivativeRealizabilityConjecture_proved

-- Independent edge-case applications of the genuine generic theorem.
example (A : NLA.IS03.RealMatrix 0) (k : ℕ) : Matrix.trace (A^k) = 0 := by
  simp [Matrix.trace]

example {n : ℕ} (A : NLA.IS03.RealMatrix n)
    (hA : NLA.IS03.EntrywiseNonnegative A) :
    NLA.IS03.EntrywiseNonnegative (A^0) ∧ 0 ≤ Matrix.trace (A^0) :=
  NLA.IS03.nonnegative_power_trace A hA 0

#assert_trust kernel NLA.IS03.derivativePolynomial_separable
#assert_trust kernel NLA.IS03.complexRoots_card
#assert_trust kernel NLA.IS03.exists_root_eigenbasis
#assert_trust kernel NLA.IS03.root_product_and_trace
#print axioms NLA.IS03.derivativePolynomial_separable
#print axioms NLA.IS03.complexRoots_card
#print axioms NLA.IS03.exists_root_eigenbasis
#print axioms NLA.IS03.root_product_and_trace
