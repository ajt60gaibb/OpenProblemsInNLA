import NLA.Proofs.RE05.OrthonormalFamily
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

#audit_named "NLA.ReviewedStatements.RE05.Successful" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.QueryBound" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.OriginalClaim" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.SourceQueryBound" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.SourceCompanion" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.AttainedOptimum" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.ReviewedStatements.RE05.Target" "Reviewed.RE05" "public" "definition"

#audit_named "NLA.Proofs.RE05.vectorMatrix" "NLA.Proofs.RE05.OrthonormalCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.vectorMatrix_matrixVector" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_vectorMatrix" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_injective" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVectorMap" "NLA.Proofs.RE05.OrthonormalCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.matrixVector_inner" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_norm" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.independent_matrixVector" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orderedMember" "NLA.Proofs.RE05.OrthonormalCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.orderedMember_orthonormal" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orderedMember_injective" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.normalized_starProjection" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.ordered_residual" "NLA.Proofs.RE05.OrthonormalCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.normalizeMatrix" "NLA.Proofs.RE05.OrthonormalFold" "public" "definition"

#audit_named "NLA.Proofs.RE05.matrixVector_normalize" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalStep" "NLA.Proofs.RE05.OrthonormalFold" "public" "definition"

#audit_named "NLA.Proofs.RE05.orthonormalList_eq_fold" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orderedPrefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "definition"

#audit_named "NLA.Proofs.RE05.inputPrefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "definition"

#audit_named "NLA.Proofs.RE05.orderedPrefix_nodup" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.sum_orderedPrefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalStep_orderedPrefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.inputPrefix_succ" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orderedPrefix_succ" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormal_fold_prefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix" "NLA.Proofs.RE05.OrthonormalFold" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalList_length" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalMember_eq_orderedMember" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalMember_orthonormal" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalMember_span" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalMember_matrix_span" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalMember_inner" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverage_trace" "NLA.Proofs.RE05.OrthonormalFamily" "public" "theorem"

noncomputable section
open scoped BigOperators Matrix InnerProductSpace
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) :
    vectorMatrix (matrixVector A) = A := by
  exact @NLA.Proofs.RE05.vectorMatrix_matrixVector n A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ}
    (v : EuclideanSpace ℝ (Fin n × Fin n)) : matrixVector (vectorMatrix v) = v := by
  exact @NLA.Proofs.RE05.matrixVector_vectorMatrix n v
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} :
    Function.Injective (matrixVector (n := n)) := by
  exact @NLA.Proofs.RE05.matrixVector_injective n
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B : Square n) :
    inner ℝ (matrixVector A) (matrixVector B) =
      NLA.Computation.LinearFamilyQuery.inner A B := by
  exact @NLA.Proofs.RE05.matrixVector_inner n A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) :
    ‖matrixVector A‖ = NLA.Computation.LinearFamilyQuery.norm n A := by
  exact @NLA.Proofs.RE05.matrixVector_norm n A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : LinearIndependent ℝ (fun j => matrixVector (P j)) := by
  exact @NLA.Proofs.RE05.independent_matrixVector n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Orthonormal ℝ (fun j => matrixVector (orderedMember P j)) := by
  exact @NLA.Proofs.RE05.orderedMember_orthonormal n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Function.Injective (orderedMember P) := by
  exact @NLA.Proofs.RE05.orderedMember_injective n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (v w : E) :
    (ℝ ∙ v).starProjection w = inner ℝ w (‖v‖⁻¹ • v) • (‖v‖⁻¹ • v) := by
  exact @NLA.Proofs.RE05.normalized_starProjection E (inferInstance) (inferInstance) v w
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (j : Fin (q + 1)) :
    InnerProductSpace.gramSchmidt ℝ (fun a => matrixVector (P a)) j =
      matrixVector (fun i k => P j i k -
        ∑ a ∈ Finset.Iio j,
          NLA.Computation.LinearFamilyQuery.inner (P j) (orderedMember P a) *
            orderedMember P a i k) := by
  exact @NLA.Proofs.RE05.ordered_residual n q P j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) :
    matrixVector (normalizeMatrix A) = ‖matrixVector A‖⁻¹ • matrixVector A := by
  exact @NLA.Proofs.RE05.matrixVector_normalize n A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) :
    orthonormalList P = (List.finRange (q + 1)).foldl (orthonormalStep P) [] := by
  exact @NLA.Proofs.RE05.orthonormalList_eq_fold n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (k : ℕ) (hk : k ≤ q + 1) : (orderedPrefix P k hk).Nodup := by
  exact @NLA.Proofs.RE05.orderedPrefix_nodup n q P hP k hk
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (j : Fin (q + 1)) (F : Square n → ℝ) :
    ∑ E ∈ (orderedPrefix P j.val (Nat.le_of_lt j.isLt)).toFinset, F E =
      ∑ a ∈ Finset.Iio j, F (orderedMember P a) := by
  exact @NLA.Proofs.RE05.sum_orderedPrefix n q P hP j F
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (j : Fin (q + 1)) :
    orthonormalStep P (orderedPrefix P j.val (Nat.le_of_lt j.isLt)) j =
      orderedPrefix P j.val (Nat.le_of_lt j.isLt) ++ [orderedMember P j] := by
  exact @NLA.Proofs.RE05.orthonormalStep_orderedPrefix n q P hP j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {q k : ℕ} (hk : k + 1 ≤ q + 1) :
    inputPrefix (q := q) (k + 1) hk =
      inputPrefix k (by omega) ++ [⟨k, by omega⟩] := by
  exact @NLA.Proofs.RE05.inputPrefix_succ q k hk
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q k : ℕ} (P : Basis n q) (hk : k + 1 ≤ q + 1) :
    orderedPrefix P (k + 1) hk =
      orderedPrefix P k (by omega) ++ [orderedMember P ⟨k, by omega⟩] := by
  exact @NLA.Proofs.RE05.orderedPrefix_succ n q k P hk
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (k : ℕ) (hk : k ≤ q + 1) :
    (inputPrefix (q := q) k hk).foldl (orthonormalStep P) [] =
      orderedPrefix P k hk := by
  exact @NLA.Proofs.RE05.orthonormal_fold_prefix n q P hP k hk
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) :
    orthonormalList P = orderedPrefix P (q + 1) le_rfl := by
  exact @NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (orthonormalList P).length = q + 1 := by
  exact @NLA.Proofs.RE05.orthonormalList_length n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (j : Fin (q + 1)) :
    orthonormalMember P j = orderedMember P j := by
  exact @NLA.Proofs.RE05.orthonormalMember_eq_orderedMember n q P hP j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) : Orthonormal ℝ (fun j => matrixVector (orthonormalMember P j)) := by
  exact @NLA.Proofs.RE05.orthonormalMember_orthonormal n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Submodule.span ℝ (Set.range (fun j => matrixVector (orthonormalMember P j))) =
      Submodule.span ℝ (Set.range (fun j => matrixVector (P j))) := by
  exact @NLA.Proofs.RE05.orthonormalMember_span n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) :
    Submodule.span ℝ (Set.range (orthonormalMember P)) =
      Submodule.span ℝ (Set.range P) := by
  exact @NLA.Proofs.RE05.orthonormalMember_matrix_span n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (a b : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P a)
      (orthonormalMember P b) = if a = b then 1 else 0 := by
  exact @NLA.Proofs.RE05.orthonormalMember_inner n q P hP a b
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ i : Fin n, leverage P i i) = (q + 1 : ℝ) := by
  exact @NLA.Proofs.RE05.leverage_trace n q P hP
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace RE05OrthonormalGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators

theorem actual_member_orthonormal {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Orthonormal ℝ (fun j : Fin (q + 1) =>
      (WithLp.toLp 2 (fun p : Fin n × Fin n => orthonormalMember P j p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin n))) :=
  NLA.Proofs.RE05.orthonormalMember_orthonormal P hP

theorem actual_member_span {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Submodule.span ℝ (Set.range (orthonormalMember P)) =
      Submodule.span ℝ (Set.range P) :=
  NLA.Proofs.RE05.orthonormalMember_matrix_span P hP

theorem actual_member_inner {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (a b : Fin (q + 1)) :
    (∑ i : Fin n, ∑ k : Fin n, orthonormalMember P a i k * orthonormalMember P b i k) =
      if a = b then 1 else 0 := NLA.Proofs.RE05.orthonormalMember_inner P hP a b

theorem literal_leverage_trace {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ i : Fin n, ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j i h) = (q + 1 : ℝ) :=
  NLA.Proofs.RE05.leverage_trace P hP

theorem literal_supplied_fold_lookup {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (j : Fin (q + 1)) :
    (((List.finRange (q + 1)).foldl (fun accepted a =>
      let v : Square n := fun i k => P a i k -
        ∑ E ∈ accepted.toFinset, NLA.Computation.LinearFamilyQuery.inner (P a) E * E i k
      let scale := NLA.Computation.LinearFamilyQuery.norm n v
      accepted ++ [if scale = 0 then (0 : Square n) else fun i k => v i k / scale]) [])[j.val]?).getD 0 =
        NLA.Proofs.RE05.orderedMember P j :=
  NLA.Proofs.RE05.orthonormalMember_eq_orderedMember P hP j

theorem zero_normalization (n : ℕ) :
    NLA.Proofs.RE05.normalizeMatrix (0 : Square n) = 0 := by
  simp [NLA.Proofs.RE05.normalizeMatrix, NLA.Computation.LinearFamilyQuery.norm,
    NLA.Computation.LinearFamilyQuery.inner]

def unitFamily : Basis 1 0 := fun _ _ _ => 1

theorem unitFamily_independent : Independent unitFamily := by
  intro c hc a
  have ha : a = 0 := by
    apply Fin.ext
    have hlt := a.isLt
    change a.val < 1 at hlt
    change a.val = 0
    omega
  subst a
  have h := hc 0 0
  simpa [unitFamily] using h

theorem unitFamily_trace : (∑ i : Fin 1, leverage unitFamily i i) = 1 := by
  simpa using NLA.Proofs.RE05.leverage_trace unitFamily unitFamily_independent

theorem preserved_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel actual_member_orthonormal
#assert_trust kernel actual_member_span
#assert_trust kernel actual_member_inner
#assert_trust kernel literal_leverage_trace
#assert_trust kernel literal_supplied_fold_lookup
#assert_trust kernel zero_normalization
#assert_trust kernel unitFamily
#assert_trust kernel unitFamily_independent
#assert_trust kernel unitFamily_trace
#assert_trust kernel preserved_target_identity
#print axioms actual_member_orthonormal
#print axioms actual_member_span
#print axioms actual_member_inner
#print axioms literal_leverage_trace
#print axioms literal_supplied_fold_lookup
#print axioms zero_normalization
#print axioms unitFamily_trace
#print axioms preserved_target_identity
end RE05OrthonormalGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.vectorMatrix
#print axioms NLA.Proofs.RE05.vectorMatrix
#assert_trust kernel NLA.Proofs.RE05.vectorMatrix_matrixVector
#print axioms NLA.Proofs.RE05.vectorMatrix_matrixVector
#assert_trust kernel NLA.Proofs.RE05.matrixVector_vectorMatrix
#print axioms NLA.Proofs.RE05.matrixVector_vectorMatrix
#assert_trust kernel NLA.Proofs.RE05.matrixVector_injective
#print axioms NLA.Proofs.RE05.matrixVector_injective
#assert_trust kernel NLA.Proofs.RE05.matrixVectorMap
#print axioms NLA.Proofs.RE05.matrixVectorMap
#assert_trust kernel NLA.Proofs.RE05.matrixVector_inner
#print axioms NLA.Proofs.RE05.matrixVector_inner
#assert_trust kernel NLA.Proofs.RE05.matrixVector_norm
#print axioms NLA.Proofs.RE05.matrixVector_norm
#assert_trust kernel NLA.Proofs.RE05.independent_matrixVector
#print axioms NLA.Proofs.RE05.independent_matrixVector
#assert_trust kernel NLA.Proofs.RE05.orderedMember
#print axioms NLA.Proofs.RE05.orderedMember
#assert_trust kernel NLA.Proofs.RE05.orderedMember_orthonormal
#print axioms NLA.Proofs.RE05.orderedMember_orthonormal
#assert_trust kernel NLA.Proofs.RE05.orderedMember_injective
#print axioms NLA.Proofs.RE05.orderedMember_injective
#assert_trust kernel NLA.Proofs.RE05.normalized_starProjection
#print axioms NLA.Proofs.RE05.normalized_starProjection
#assert_trust kernel NLA.Proofs.RE05.ordered_residual
#print axioms NLA.Proofs.RE05.ordered_residual
#assert_trust kernel NLA.Proofs.RE05.normalizeMatrix
#print axioms NLA.Proofs.RE05.normalizeMatrix
#assert_trust kernel NLA.Proofs.RE05.matrixVector_normalize
#print axioms NLA.Proofs.RE05.matrixVector_normalize
#assert_trust kernel NLA.Proofs.RE05.orthonormalStep
#print axioms NLA.Proofs.RE05.orthonormalStep
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_eq_fold
#print axioms NLA.Proofs.RE05.orthonormalList_eq_fold
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix
#print axioms NLA.Proofs.RE05.orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.inputPrefix
#print axioms NLA.Proofs.RE05.inputPrefix
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix_nodup
#print axioms NLA.Proofs.RE05.orderedPrefix_nodup
#assert_trust kernel NLA.Proofs.RE05.sum_orderedPrefix
#print axioms NLA.Proofs.RE05.sum_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalStep_orderedPrefix
#print axioms NLA.Proofs.RE05.orthonormalStep_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.inputPrefix_succ
#print axioms NLA.Proofs.RE05.inputPrefix_succ
#assert_trust kernel NLA.Proofs.RE05.orderedPrefix_succ
#print axioms NLA.Proofs.RE05.orderedPrefix_succ
#assert_trust kernel NLA.Proofs.RE05.orthonormal_fold_prefix
#print axioms NLA.Proofs.RE05.orthonormal_fold_prefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix
#print axioms NLA.Proofs.RE05.orthonormalList_eq_orderedPrefix
#assert_trust kernel NLA.Proofs.RE05.orthonormalList_length
#print axioms NLA.Proofs.RE05.orthonormalList_length
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_eq_orderedMember
#print axioms NLA.Proofs.RE05.orthonormalMember_eq_orderedMember
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_orthonormal
#print axioms NLA.Proofs.RE05.orthonormalMember_orthonormal
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_span
#print axioms NLA.Proofs.RE05.orthonormalMember_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_matrix_span
#print axioms NLA.Proofs.RE05.orthonormalMember_matrix_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalMember_inner
#print axioms NLA.Proofs.RE05.orthonormalMember_inner
#assert_trust kernel NLA.Proofs.RE05.leverage_trace
#print axioms NLA.Proofs.RE05.leverage_trace

end
