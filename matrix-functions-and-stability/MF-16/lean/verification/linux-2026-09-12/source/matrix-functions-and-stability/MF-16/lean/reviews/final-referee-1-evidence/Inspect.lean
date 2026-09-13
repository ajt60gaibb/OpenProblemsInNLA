/- Independent final mathematical referee: /root/mf16_final_referee.
Generic Lean environment traversal follows the repository's IS-03 referee
inspection pattern. The MF-16 final-root path and semantic requirements below
were selected independently after reading the original target and full proof.
This file is a review diagnostic and is never imported by the solution. -/
import Solution
import Lean.Util.FoldConsts

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exports := [``NLA.MF16.word_semantics, ``NLA.MF16.source_data,
    ``NLA.MF16.twelfth_power_reduction, ``NLA.MF16.polynomial_word_equivalence,
    ``NLA.MF16.krawczyk_certificate, ``NLA.MF16.certified_root,
    ``NLA.MF16.root_to_matrix, ``NLA.MF16.counterexample,
    ``NLA.MF16.not_wordUniquenessConjecture]
  let library := [``LeanCert.Engine.krawczykCheck_sound,
    ``LeanCert.Engine.fixedPoint_iff_systemZero,
    ``LeanCert.Engine.contraction_unique_fixedPoint_in_finBox,
    ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
    ``LeanCert.Engine.newtonMap_fderiv_norm_le,
    ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
    ``LeanCert.Engine.newtonMap_center_mem,
    ``LeanCert.Engine.systemEval_mem_pointEvalIntervals]
  let isProject := fun n : Name => n.toString.startsWith "NLA.MF16." ||
    n.toString.startsWith "_private.NLA.MF16."
  for (label, starts) in [("FINAL_TARGET", [``NLA.MF16.not_wordUniquenessConjecture]),
      ("ALL_EXPORTS", exports)] do
    let mut pending := starts
    let mut seen : List Name := []
    let mut used : List Name := []
    for _ in [:5000] do
      match pending with
      | [] => pure ()
      | name :: rest =>
        pending := rest
        unless seen.contains name do
          seen := name :: seen
          let some ci := env.find? name | throwError "Missing retained declaration: {name}"
          if ci.isUnsafe || ci.isPartial then
            throwError "Unsafe/partial retained declaration: {name}"
          for ax in (← liftCoreM <| collectAxioms name) do
            unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
              throwError "Forbidden transitive axiom: {name}: {ax}"
          let body ← match ci.value? (allowOpaque := true) with
            | some b => pure b.getUsedConstants.toList
            | none => match ci with
              | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
              | _ => throwError "Unexplained bodyless declaration: {name}"
          let deps := ci.type.getUsedConstants.toList ++ body
          used := deps ++ used
          let follow := deps.filter fun n => isProject n || library.contains n
          logInfo m!"REFEREE_EDGE {label} {name}: {follow}"
          pending := follow ++ pending
    unless pending.isEmpty do throwError "Traversal incomplete: {label}"
    for need in [``NLA.MF16.actual_krawczyk_checked,
      ``NLA.MF16.certified_root_proved,
      ``NLA.MF16.polynomial_word_equivalence_proved,
      ``NLA.MF16.polynomial_reduced_equivalence,
      ``NLA.MF16.polynomial_eval_zero, ``NLA.MF16.polynomial_eval_one,
      ``NLA.MF16.polynomial_eval_two,
      ``NLA.MF16.matrix_twelfth_power_of_det_three,
      ``NLA.MF16.complexify_two_by_two_posDef,
      ``NLA.MF16.complexify_witness_eval,
      ``NLA.MF16.word_eq_of_two_entries,
      ``NLA.MF16.witness_word_det, ``NLA.MF16.witness_word_transpose,
      ``NLA.MF16.matrix_recovery_from_equations,
      ``NLA.MF16.box_first_coordinate_gt_three,
      ``Matrix.aeval_self_charpoly, ``Matrix.charpoly_fin_two,
      ``Matrix.PosDef.conjTranspose_mul_mul_same,
      ``Matrix.PosDef.diagonal, ``Matrix.map_mul, ``Matrix.map_pow,
      ``Matrix.det_mul, ``Matrix.det_pow,
      ``LeanCert.Engine.krawczykCheck_sound,
      ``LeanCert.Engine.fixedPoint_iff_systemZero,
      ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
      ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
      ``LeanCert.Engine.newtonMap_fderiv_norm_le,
      ``LeanCert.Engine.evalIntervalCore_correct,
      ``ContractingWith.exists_fixedPoint'] do
      unless used.contains need do
        throwError "Final proof path fails to consume {need} in {label}"
      logInfo m!"REFEREE_REQUIRED {label}: {need}"
    logInfo m!"REFEREE_COUNTS {label}: project={(seen.filter isProject).length}, library={(seen.filter (fun n => !isProject n)).length}"

#check NLA.MF16.word_semantics
#check NLA.MF16.source_data
#check NLA.MF16.twelfth_power_reduction
#check NLA.MF16.polynomial_word_equivalence
#check NLA.MF16.krawczyk_certificate
#check NLA.MF16.certified_root
#check NLA.MF16.root_to_matrix
#check NLA.MF16.counterexample
#check NLA.MF16.not_wordUniquenessConjecture
set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
#print NLA.MF16.SymmetricWord
#print NLA.MF16.evalWord
#print Matrix.PosDef
#print LeanCert.Engine.SystemZero
#print LeanCert.Engine.FinBoxMem
set_option pp.proofs true in
#print NLA.MF16.certified_root_proved
set_option pp.proofs true in
#print NLA.MF16.not_wordUniquenessConjecture_proved

#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#assert_trust kernel NLA.MF16.complexify_two_by_two_posDef
#assert_trust kernel NLA.MF16.polynomial_reduced_equivalence
#assert_trust kernel NLA.MF16.word_eq_of_two_entries
#print axioms LeanCert.Engine.krawczykCheck_sound
#print axioms NLA.MF16.complexify_two_by_two_posDef
#print axioms NLA.MF16.polynomial_reduced_equivalence
#print axioms NLA.MF16.word_eq_of_two_entries

-- Concrete noncommuting inputs and a non-vacuous all-complex uniqueness target
-- are already proved by source_data and the final counterexample. This is an
-- independent fully expanded direct consumer of the final negation.
open scoped ComplexOrder in
example : ¬ (∀ w : List NLA.MF16.Letter, w = w.reverse ∧ .X ∈ w →
    ∀ B P : Matrix (Fin 2) (Fin 2) ℂ, B.PosDef → P.PosDef →
    ∃! X : Matrix (Fin 2) (Fin 2) ℂ, X.PosDef ∧
      (w.map (fun l => match l with | .X => X | .B => B)).prod = P) :=
  NLA.MF16.not_wordUniquenessConjecture

namespace RefereeMF16Diagnostic
open NLA.MF16 LeanCert.Core LeanCert.Engine
def q (r : ℚ) : Lean.Json := .str (toString r.num ++ "/" ++ toString r.den)
def interval (I : IntervalRat) : Lean.Json := .arr #[q I.lo, q I.hi]
def vector {n : ℕ} (v : Fin n → ℚ) : Lean.Json := .arr ((List.ofFn v).map q).toArray
def ivec {n : ℕ} (v : Fin n → IntervalRat) : Lean.Json :=
  .arr ((List.ofFn v).map interval).toArray
def matrix {n : ℕ} (M : Matrix (Fin n) (Fin n) ℚ) : Lean.Json :=
  .arr ((List.ofFn M).map vector).toArray
def imatrix {n : ℕ} (M : Matrix (Fin n) (Fin n) IntervalRat) : Lean.Json :=
  .arr ((List.ofFn M).map ivec).toArray
def ast : Expr → Lean.Json
  | .const r => .arr #[.str "const", q r]
  | .var i => .arr #[.str "var", Lean.toJson i]
  | .add a b => .arr #[.str "add", ast a, ast b]
  | .mul a b => .arr #[.str "mul", ast a, ast b]
  | .neg a => .arr #[.str "neg", ast a]
  | _ => .str "UNSUPPORTED"

#eval IO.println ("REFEREE_NUMERIC_JSON=" ++ (Lean.Json.mkObj [
  ("AST", .arr ((List.ofFn polynomialSystem).map ast).toArray),
  ("center", vector rootCenter), ("box", ivec rootBox),
  ("C", matrix rootCertificate.preconditioner),
  ("J", imatrix (intervalJacobian polynomialSystem rootBox {})),
  ("I-CJ", imatrix (preconditionedJacobian rootCertificate.preconditioner
    (intervalJacobian polynomialSystem rootBox {}))),
  ("radius", q (boxRadius rootBox rootCenter)),
  ("q", q contractionBound),
  ("newton_center", ivec (newtonCenterInterval polynomialSystem rootCenter
    rootCertificate.preconditioner {})),
  ("image", ivec (newtonImageEnclosure polynomialSystem rootBox rootCenter
    rootCertificate.preconditioner {}))
]).compress)
end RefereeMF16Diagnostic
