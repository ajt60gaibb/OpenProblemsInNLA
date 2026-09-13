/- Independent final referee 2: actual MF16 target, proof and numerical inputs.
This module is review evidence, not part of the submitted solution. -/
import Solution
import Lean.Util.FoldConsts

open scoped ComplexOrder
open LeanCert.Core LeanCert.Engine
namespace MF16RefereeTwo

example : NLA.MF16.WordUniquenessConjecture =
    (∀ w : List NLA.MF16.Letter,
      (w = w.reverse ∧ NLA.MF16.Letter.X ∈ w) →
      ∀ B P : Matrix (Fin 2) (Fin 2) ℂ, Matrix.PosDef B → Matrix.PosDef P →
      ∃! X : Matrix (Fin 2) (Fin 2) ℂ, Matrix.PosDef X ∧
        (w.map (fun letter => match letter with
          | .X => X | .B => B)).prod = P) := rfl

private def qjson (q : ℚ) : Lean.Json :=
  Lean.Json.arr #[Lean.Json.str (toString q.num), Lean.Json.str (toString q.den)]
private def ijson (i : IntervalRat) : Lean.Json := Lean.Json.arr #[qjson i.lo,qjson i.hi]
private def ejson : Expr → Lean.Json
  | .const q => Lean.Json.arr #[.str "const", qjson q]
  | .var i => Lean.Json.arr #[.str "var", .str (toString i)]
  | .add a b => Lean.Json.arr #[.str "add", ejson a,ejson b]
  | .mul a b => Lean.Json.arr #[.str "mul", ejson a,ejson b]
  | .neg a => Lean.Json.arr #[.str "neg",ejson a]
  | _ => .str "UNSUPPORTED"
private def actualData : Lean.Json := Lean.Json.mkObj [
  ("F",.arr (Array.ofFn fun i : Fin 3 => ejson (NLA.MF16.polynomialSystem i))),
  ("center",.arr (Array.ofFn fun i => qjson (NLA.MF16.rootCenter i))),
  ("box",.arr (Array.ofFn fun i => ijson (NLA.MF16.rootBox i))),
  ("C",.arr (Array.ofFn fun i => .arr (Array.ofFn fun j => qjson (NLA.MF16.rootCertificate.preconditioner i j)))),
  ("J",.arr (Array.ofFn fun i => .arr (Array.ofFn fun j => ijson
    (intervalJacobian NLA.MF16.polynomialSystem NLA.MF16.rootBox {} i j)))),
  ("q",qjson NLA.MF16.contractionBound),
  ("newtonImage",.arr (Array.ofFn fun i => ijson (newtonImageEnclosure
    NLA.MF16.polynomialSystem NLA.MF16.rootBox NLA.MF16.rootCenter
    NLA.MF16.rootCertificate.preconditioner {} i))),
  ("radius",qjson (boxRadius NLA.MF16.rootBox NLA.MF16.rootCenter))]
#eval IO.println ("ACTUAL_DATA " ++ actualData.compress)
end MF16RefereeTwo

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let selected := [``LeanCert.Engine.krawczykCheck_sound,
    ``LeanCert.Engine.contraction_unique_fixedPoint_in_finBox,
    ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
    ``LeanCert.Engine.newtonMap_fderiv_norm_le,
    ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
    ``LeanCert.Engine.newtonMap_differentiable,
    ``LeanCert.Engine.systemEval_differentiable,
    ``LeanCert.Engine.evalFin_differentiable,
    ``LeanCert.Engine.fixedPoint_iff_systemZero,
    ``LeanCert.Engine.newtonMap_center_mem,
    ``LeanCert.Engine.systemEval_mem_pointEvalIntervals]
  let project := fun n : Name => n.toString.startsWith "NLA.MF16." ||
    n.toString.startsWith "_private.NLA.MF16."
  let mut pending := [``NLA.MF16.not_wordUniquenessConjecture]
  let mut seen : List Name := []
  let mut dependencies : List Name := []
  for _ in [:3000] do
    match pending with
    | [] => pure ()
    | name :: rest =>
      pending := rest
      unless seen.contains name do
        seen := name :: seen
        let some info := env.find? name | throwError "Missing {name}"
        if info.isUnsafe || info.isPartial then throwError "Unsafe/partial {name}"
        let axs ← liftCoreM <| collectAxioms name
        for ax in axs do
          unless [``propext,``Classical.choice,``Quot.sound].contains ax do
            throwError "Unexpected transitive axiom {name}: {ax}"
        let body ← match info.value? (allowOpaque := true) with
          | some b => pure b.getUsedConstants.toList
          | none => match info with
            | .inductInfo _ | .ctorInfo _ | .recInfo _ => pure []
            | _ => throwError "Bodyless {name}"
        let used := info.type.getUsedConstants.toList ++ body
        dependencies := used ++ dependencies
        let ds := used.filter (fun n => project n || selected.contains n)
        logInfo m!"ACTUAL_EDGE {name}: {ds}"
        pending := ds ++ pending
  unless pending.isEmpty do throwError "Incomplete traversal"
  for name in [``NLA.MF16.actual_krawczyk_checked,
      ``NLA.MF16.certified_root_proved,``NLA.MF16.polynomial_word_equivalence_proved,
      ``NLA.MF16.polynomial_eval_zero,``NLA.MF16.polynomial_eval_one,``NLA.MF16.polynomial_eval_two,
      ``NLA.MF16.matrix_twelfth_power_of_det_three,``Matrix.aeval_self_charpoly,
      ``Matrix.charpoly_fin_two,``NLA.MF16.word_eq_of_two_entries,
      ``NLA.MF16.witness_word_transpose,``NLA.MF16.witness_word_det,
      ``NLA.MF16.complexify_two_by_two_posDef,``Matrix.PosDef.conjTranspose_mul_mul_same,
      ``NLA.MF16.complexify_pow,``NLA.MF16.complexify_mul,
      ``NLA.MF16.root_to_matrix_proved,``NLA.MF16.counterexample_proved,
      ``NLA.MF16.not_wordUniquenessConjecture_proved,
      ``LeanCert.Engine.krawczykCheck_sound,``LeanCert.Engine.fixedPoint_iff_systemZero,
      ``LeanCert.Engine.contraction_unique_fixedPoint_in_finBox,
      ``LeanCert.Engine.jacobianAt_mem_intervalJacobian,
      ``LeanCert.Engine.newtonMap_mapsTo_of_imageEnclosure,
      ``LeanCert.Engine.newtonMap_fderiv_norm_le,
      ``LeanCert.Engine.evalIntervalCore_correct,``ContractingWith.exists_fixedPoint'] do
    unless dependencies.contains name do throwError "Not retained: {name}"
    logInfo m!"RETAINED {name}"
  logInfo m!"REVIEW_PROJECT_COUNT {(seen.filter project).length}"
  logInfo m!"REVIEW_LIBRARY_COUNT {(seen.filter (fun n => !project n)).length}"

set_option pp.all true in
#print NLA.MF16.WordUniquenessConjecture
set_option pp.all true in
#print Matrix.PosDef
set_option pp.proofs true in
#print NLA.MF16.actual_krawczyk_checked._proof_1_1
set_option pp.proofs true in
#print NLA.MF16.certified_root_proved
set_option pp.proofs true in
#print NLA.MF16.root_to_matrix_proved
set_option pp.proofs true in
#print NLA.MF16.not_wordUniquenessConjecture_proved
#assert_trust kernel NLA.MF16.actual_krawczyk_checked._proof_1_1
#assert_trust kernel LeanCert.Engine.krawczykCheck_sound
#assert_trust kernel NLA.MF16.complexify_two_by_two_posDef
#assert_trust kernel NLA.MF16.word_eq_of_two_entries
#print axioms NLA.MF16.actual_krawczyk_checked._proof_1_1
#print axioms LeanCert.Engine.krawczykCheck_sound
#print axioms NLA.MF16.complexify_two_by_two_posDef
#print axioms NLA.MF16.word_eq_of_two_entries
