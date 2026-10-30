import NLA.Proofs.RE05.MedianRobust
import Reviewed.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
open Lean Elab Command in
elab "#audit_named " user:str modName:str visibility:str expected:str : command => do
  unless visibility.getString == "public" || visibility.getString == "private" || visibility.getString == "local" do
    throwErrorAt visibility "unsupported visibility"
  let decl := if visibility.getString == "private" then
    Lean.mkPrivateNameCore modName.getString.toName user.getString.toName
    else user.getString.toName
  let some info := (← getEnv).find? decl | throwErrorAt user "missing exact compiler constant {decl}"
  match expected.getString, info with
  | "theorem", .thmInfo _ => pure ()
  | "definition", .defnInfo _ => pure ()
  | "inductive", .inductInfo _ => pure ()
  | _, _ => throwErrorAt user "constant kind differs from frozen source"
  logInfo m!"AUDITED_KIND {decl.toString} {expected.getString}"
  logInfo m!"AUDITED_ACTUAL {user.getString} {decl.toString} {visibility.getString}"
  elabCommand (← `(#assert_trust $(mkIdent `kernel) $(mkIdent decl)))
  elabCommand (← `(#print axioms $(mkIdent decl)))
  let axs ← liftCoreM <| collectAxioms decl
  let body := String.intercalate "," (axs.toList.map Name.toString)
  logInfo m!"AUDITED_AXIOMS {decl.toString} [{body}]"
#audit_named "NLA.Computation.SVDMachine.Instruction" "NLA.Computation.SVDMachine" "public" "inductive"

#audit_named "NLA.Computation.SVDMachine.Program" "NLA.Computation.SVDMachine" "public" "inductive"

#audit_named "NLA.Computation.SVDMachine.Status" "NLA.Computation.SVDMachine" "public" "inductive"

#audit_named "NLA.Computation.SVDMachine.State" "NLA.Computation.SVDMachine" "public" "inductive"

#audit_named "NLA.Computation.SVDMachine.initial" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.ordinaryStep" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.ValidSVD" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.DisjointBlocks" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.OutputBlocksDisjoint" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.matrixCell" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.readMatrix" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.writeSVD" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.charge" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.Step" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.Trace" "NLA.Computation.SVDMachine" "public" "inductive"

#audit_named "NLA.Computation.SVDMachine.LegalTrace" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.SVDMachine.CostThrough" "NLA.Computation.SVDMachine" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.Family" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.Side" "NLA.Computation.NonadaptiveMatrixQuery" "public" "inductive"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.Query" "NLA.Computation.NonadaptiveMatrixQuery" "public" "inductive"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.answer" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.standardBasis" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.Plan" "NLA.Computation.NonadaptiveMatrixQuery" "public" "inductive"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.queryList" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.GaussianLaw" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.logWidth" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.rootWidth" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.firstWidth" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.secondWidth" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.thirdWidth" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.makePlan" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.oracleAnswers" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.storedVector" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.minimumIndex" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.squaredFrobenius" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.frobenius" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.optimum" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.SVDResult" "NLA.Computation.NonadaptiveMatrixQuery" "public" "inductive"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.ValidSVDResult" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.exactSVD" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.postprocess" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.run" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.QueryBound" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.Successful" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.NonadaptiveMatrixQuery.SVDTotal" "NLA.Computation.NonadaptiveMatrixQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.Square" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.Basis" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.Independent" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.represent" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.inner" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.norm" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.orthonormalList" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.orthonormalMember" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.leverage" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.squaredAccuracy" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.baseWidth" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.threshold" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.gaussianWidth" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.Plan" "NLA.Computation.LinearFamilyQuery" "public" "inductive"

#audit_named "NLA.Computation.LinearFamilyQuery.makePlan" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.queries" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.plans" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.batchQueries" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.batchAnswers" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.dot" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.uColumn" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.complement" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.predictedLeft" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.predictedRight" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.observedLeft" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.observedRight" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.gram" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.rhs" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.singleOutput" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.responseOffset" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.copyResponses" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.copyOutput" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.coefficientDistance" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.medianRadius" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.chooseCopy" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.postprocess" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.run" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Computation.LinearFamilyQuery.optimum" "NLA.Computation.LinearFamilyQuery" "public" "definition"

#audit_named "NLA.Statements.RE05.Successful" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.QueryBound" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.OriginalClaim" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.SourceQueryBound" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.SourceCompanion" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.AttainedOptimum" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Statements.RE05.Target" "NLA.Statements.RE05" "public" "definition"

#audit_named "NLA.Proofs.RE05.matrixVector" "NLA.Proofs.RE05.Attained" "public" "definition"

#audit_named "NLA.Proofs.RE05.representationMap" "NLA.Proofs.RE05.Attained" "public" "definition"

#audit_named "NLA.Proofs.RE05.frobenius_eq_norm" "NLA.Proofs.RE05.Attained" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_frobenius_minimum" "NLA.Proofs.RE05.Attained" "public" "theorem"

#audit_named "NLA.Proofs.RE05.attained_optimum" "NLA.Proofs.RE05.Attained" "public" "theorem"

#audit_named "NLA.Proofs.RE05.attainedOptimum" "NLA.Proofs.RE05.Attained" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_sub" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frobenius_eq_zero_iff" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frobenius_triangle" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_orthogonal_optimum" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_pythagorean_optimum" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.optimum_eq_zero_iff" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.sorted_get_le_of_count" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.sorted_count_le_get" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.medianRadius_le_of_eight" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.medianRadius_eight" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.foldl_score_minimum" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.chooseCopy_le" "NLA.Proofs.RE05.MedianRadius" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientDistance_symm" "NLA.Proofs.RE05.MedianRobust" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientDistance_triangle" "NLA.Proofs.RE05.MedianRobust" "public" "theorem"

#audit_named "NLA.Proofs.RE05.eight_intersection" "NLA.Proofs.RE05.MedianRobust" "public" "theorem"

#audit_named "NLA.Proofs.RE05.postprocess_distance_of_eight" "NLA.Proofs.RE05.MedianRobust" "public" "theorem"

#audit_named "NLA.Proofs.RE05.postprocess_relative_of_eight" "NLA.Proofs.RE05.MedianRobust" "public" "theorem"

#audit_named "NLA.ReviewedStatements.RE05.Successful" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.QueryBound" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.OriginalClaim" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.SourceQueryBound" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.SourceCompanion" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.AttainedOptimum" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.Target" "Reviewed.RE05" "public" "definition"

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length) (b : ℝ)
    (hc : k + 1 ≤ l.countP (fun x => decide (x ≤ b))) : l[k] ≤ b := by
  exact @NLA.Proofs.RE05.sorted_get_le_of_count l hs k hk b hc
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example (l : List ℝ) (hs : l.Pairwise (· ≤ ·))
    (k : ℕ) (hk : k < l.length) :
    k + 1 ≤ l.countP (fun x => decide (x ≤ l[k])) := by
  exact @NLA.Proofs.RE05.sorted_count_le_get l hs k hk
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) (b : ℝ)
    (h : 8 ≤ (Finset.univ.filter fun other : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses copy)
        (copyOutput P schedule responses other) ≤ b).card) :
    medianRadius P schedule responses copy ≤ b := by
  exact @NLA.Proofs.RE05.medianRadius_le_of_eight n q P schedule responses copy b h
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (copy : Fin 15) :
    8 ≤ (Finset.univ.filter fun other : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses copy)
        (copyOutput P schedule responses other) ≤
          medianRadius P schedule responses copy).card := by
  exact @NLA.Proofs.RE05.medianRadius_eight n q P schedule responses copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {α : Type*} (score : α → ℝ) (l : List α) (best : α) :
    score (l.foldl (fun b x => if score x < score b then x else b) best) ≤ score best ∧
    ∀ x ∈ l, score (l.foldl (fun b x => if score x < score b then x else b) best) ≤
      score x := by
  exact @NLA.Proofs.RE05.foldl_score_minimum α score l best
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ)) (copy : Fin 15) :
    medianRadius P schedule responses (chooseCopy P schedule responses) ≤
      medianRadius P schedule responses copy := by
  exact @NLA.Proofs.RE05.chooseCopy_le n q P schedule responses copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (x y : Fin (q + 1) → ℝ) :
    coefficientDistance P x y = coefficientDistance P y x := by
  exact @NLA.Proofs.RE05.coefficientDistance_symm n q P x y
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (x y z : Fin (q + 1) → ℝ) :
    coefficientDistance P x z ≤ coefficientDistance P x y + coefficientDistance P y z := by
  exact @NLA.Proofs.RE05.coefficientDistance_triangle n q P x y z
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example (s t : Finset (Fin 15)) (hs : 8 ≤ s.card) (ht : 8 ≤ t.card) :
    ∃ j, j ∈ s ∧ j ∈ t := by
  exact @NLA.Proofs.RE05.eight_intersection s t hs ht
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (center : Fin (q + 1) → ℝ) (ρ : ℝ)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ).card) :
    coefficientDistance P (postprocess P schedule responses) center ≤ 3 * ρ := by
  exact @NLA.Proofs.RE05.postprocess_distance_of_eight n q P schedule responses center ρ hgood
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (A : Square n) (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (postprocess P schedule responses)) ≤
        (1 + ε) * NLA.Computation.LinearFamilyQuery.optimum P A := by
  exact @NLA.Proofs.RE05.postprocess_relative_of_eight n q P A schedule responses ε hε hgood
end NLA.Proofs.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

example (l : List ℝ) (hs : l.Pairwise (· ≤ ·)) (k : ℕ) (hk : k < l.length)
    (b : ℝ) (hc : k + 1 ≤ l.countP (fun x => decide (x ≤ b))) : l[k] ≤ b :=
  sorted_get_le_of_count l hs k hk b hc

example (s t : Finset (Fin 15)) (hs : 8 ≤ s.card) (ht : 8 ≤ t.card) :
    ∃ j, j ∈ s ∧ j ∈ t := eight_intersection s t hs ht

example {n q : ℕ} (P : Basis n q) (schedule : Fin 15 → Plan n)
    (responses : List (Fin n → ℝ)) (center : Fin (q + 1) → ℝ) (ρ : ℝ)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      coefficientDistance P (copyOutput P schedule responses j) center ≤ ρ).card) :
    coefficientDistance P (postprocess P schedule responses) center ≤ 3 * ρ :=
  postprocess_distance_of_eight P schedule responses center ρ hgood

example {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (postprocess P schedule responses)) ≤
      (1 + ε) * NLA.Computation.LinearFamilyQuery.optimum P A :=
  postprocess_relative_of_eight P A schedule responses ε hε hgood

-- Exact membership/zero-optimum specialization of the same actual selector.
example {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (responses : List (Fin n → ℝ))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hz : NLA.Computation.LinearFamilyQuery.optimum P A = 0)
    (hgood : 8 ≤ (Finset.univ.filter fun j : Fin 15 =>
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent P (copyOutput P schedule responses j)) ^ 2 ≤
      (1 + squaredAccuracy ε) * NLA.Computation.LinearFamilyQuery.optimum P A ^ 2).card) :
    A = represent P (postprocess P schedule responses) := by
  have h := postprocess_relative_of_eight P A schedule responses ε hε hgood
  rw [hz, mul_zero] at h
  apply (frobenius_eq_zero_iff A _).mp
  exact le_antisymm h (Real.sqrt_nonneg _)

#assert_trust kernel sorted_get_le_of_count
#assert_trust kernel sorted_count_le_get
#assert_trust kernel medianRadius_le_of_eight
#assert_trust kernel medianRadius_eight
#assert_trust kernel foldl_score_minimum
#assert_trust kernel chooseCopy_le
#assert_trust kernel coefficientDistance_symm
#assert_trust kernel coefficientDistance_triangle
#assert_trust kernel eight_intersection
#assert_trust kernel postprocess_distance_of_eight
#assert_trust kernel postprocess_relative_of_eight
#print axioms sorted_get_le_of_count
#print axioms sorted_count_le_get
#print axioms medianRadius_le_of_eight
#print axioms medianRadius_eight
#print axioms foldl_score_minimum
#print axioms chooseCopy_le
#print axioms coefficientDistance_symm
#print axioms coefficientDistance_triangle
#print axioms eight_intersection
#print axioms postprocess_distance_of_eight
#print axioms postprocess_relative_of_eight

end
