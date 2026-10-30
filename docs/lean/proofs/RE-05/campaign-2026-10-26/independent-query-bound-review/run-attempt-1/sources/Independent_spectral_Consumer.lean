import NLA.Proofs.RE05.SelectedCharge
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

#audit_named "NLA.Proofs.RE05.leverage_eq_sum_gram" "NLA.Proofs.RE05.LeveragePSD" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverage_symmetric" "NLA.Proofs.RE05.LeveragePSD" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverage_posSemidef" "NLA.Proofs.RE05.LeveragePSD" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.Space" "NLA.Proofs.TR04.SVDCore" "public" "definition"

#audit_named "NLA.Proofs.TR04.SVD.rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "definition"

#audit_named "NLA.Proofs.TR04.SVD.norm_image_rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.inner_image_rightBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.image_rightBasis_eq_zero" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.range_finrank_le_domain" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.range_finrank_le_codomain" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.leftVector" "NLA.Proofs.TR04.SVDCore" "public" "definition"

#audit_named "NLA.Proofs.TR04.SVD.orthonormal_leftVector_positive" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.exists_leftBasis" "NLA.Proofs.TR04.SVDCore" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.image_rightBasis_eq_smul" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.sum_fin_truncate" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"

#audit_named "NLA.Proofs.TR04.SVD.exists_validSVD" "NLA.Proofs.TR04.SVDTotal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.svd_total" "NLA.Proofs.RE05.SVDTotal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.squareSingularValues" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "definition"

#audit_named "NLA.Proofs.RE05.validSVD_square_reconstruct" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_square_mulVec_right" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_posSemidef_weighted_column" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_posSemidef_trace" "NLA.Proofs.RE05.PositiveSVDTrace" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selectedCount" "NLA.Proofs.RE05.QueryCount" "public" "definition"

#audit_named "NLA.Proofs.RE05.batchQueries_length" "NLA.Proofs.RE05.QueryCount" "public" "theorem"

#audit_named "NLA.Proofs.RE05.baseWidth_positive" "NLA.Proofs.RE05.QueryCount" "public" "theorem"

#audit_named "NLA.Proofs.RE05.threshold_mul_width" "NLA.Proofs.RE05.QueryCount" "public" "theorem"

#audit_named "NLA.Proofs.RE05.sourceQueryBound_of_selected_charge" "NLA.Proofs.RE05.QueryCount" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exactSVD_posSemidef_trace" "NLA.Proofs.RE05.SelectedCharge" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exactSVD_leverage_sum" "NLA.Proofs.RE05.SelectedCharge" "public" "theorem"

#audit_named "NLA.Proofs.RE05.filter_selected_charge" "NLA.Proofs.RE05.SelectedCharge" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selectedCount_charge" "NLA.Proofs.RE05.SelectedCharge" "public" "theorem"

#audit_named "NLA.Proofs.RE05.sourceQueryBound" "NLA.Proofs.RE05.SelectedCharge" "public" "theorem"

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
example {n q : ℕ} (P : Basis n q) :
    leverage P = ∑ j : Fin (q + 1),
      orthonormalMember P j * (orthonormalMember P j).transpose := by
  exact @NLA.Proofs.RE05.leverage_eq_sum_gram n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) : (leverage P).IsSymm := by
  exact @NLA.Proofs.RE05.leverage_symmetric n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) : (leverage P).PosSemidef := by
  exact @NLA.Proofs.RE05.leverage_posSemidef n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ} {B U V : Matrix (Fin n) (Fin n) ℝ}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) (i j : Fin n) :
    B i j = ∑ k : Fin n, U i k * squareSingularValues sigma k * V j k := by
  exact @NLA.Proofs.RE05.validSVD_square_reconstruct n B U V sigma h i j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ} {B U V : Matrix (Fin n) (Fin n) ℝ}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) (j : Fin n) :
    B *ᵥ (fun a => V a j) = fun i => squareSingularValues sigma j * U i j := by
  exact @NLA.Proofs.RE05.validSVD_square_mulVec_right n B U V sigma h j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (j : Fin n) :
    B.transpose *ᵥ (fun a => U a j) =
      fun i => squareSingularValues sigma j * V i j := by
  exact @NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left n B U V sigma h j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j : Fin n) :
    squareSingularValues sigma j * (∑ i : Fin n, U i j * V i j) =
      squareSingularValues sigma j := by
  exact @NLA.Proofs.RE05.validSVD_posSemidef_weighted_column n B U V sigma h hB j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    B.trace = ∑ j : Fin n, squareSingularValues sigma j := by
  exact @NLA.Proofs.RE05.validSVD_posSemidef_trace n B U V sigma h hB
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n : ℕ} (B : Square n) (hB : B.PosSemidef) :
    B.trace = ∑ j : Fin n, (exactSVD B).sigma (Fin.cast (Nat.min_self n).symm j) := by
  exact @NLA.Proofs.RE05.exactSVD_posSemidef_trace n B hB
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ j : Fin n, (exactSVD (leverage P)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = (q + 1 : ℝ) := by
  exact @NLA.Proofs.RE05.exactSVD_leverage_sum n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n : ℕ} (sigma : Fin n → ℝ)
    (hsigma : ∀ j, 0 ≤ sigma j) (t : ℝ) :
    (((List.finRange n).filter fun j => t < sigma j).length : ℝ) * t ≤
      ∑ j : Fin n, sigma j := by
  exact @NLA.Proofs.RE05.filter_selected_charge n sigma hsigma t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ) :
    (selectedCount P ε : ℝ) * threshold q (squaredAccuracy ε) ≤ (q + 1 : ℕ) := by
  exact @NLA.Proofs.RE05.selectedCount_charge n q P hP ε
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ε : ℝ) (hε : 0 < ε) : NLA.Statements.RE05.SourceQueryBound P ε := by
  exact @NLA.Proofs.RE05.sourceQueryBound n q P hP ε hε
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace RE05SpectralGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
open NLA.Computation.SVDMachine
open scoped BigOperators Matrix

theorem literal_leverage_symmetric {n q : ℕ} (P : Basis n q) :
    Matrix.IsSymm (fun i k => ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j k h : Square n) :=
  NLA.Proofs.RE05.leverage_symmetric P

theorem literal_leverage_psd {n q : ℕ} (P : Basis n q) :
    Matrix.PosSemidef (fun i k => ∑ j : Fin (q + 1), ∑ h : Fin n,
      orthonormalMember P j i h * orthonormalMember P j k h : Square n) :=
  NLA.Proofs.RE05.leverage_posSemidef P

theorem literal_actual_singular_sum {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    (∑ j : Fin n, (exactSVD (leverage P)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = (q + 1 : ℝ) :=
  NLA.Proofs.RE05.exactSVD_leverage_sum P hP

theorem literal_actual_selected_charge {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (ε : ℝ) :
    (((List.finRange n).filter (fun j => threshold q (squaredAccuracy ε) <
      (exactSVD (leverage P)).sigma (Fin.cast (Nat.min_self n).symm j))).length : ℝ) *
        threshold q (squaredAccuracy ε) ≤ (q + 1 : ℕ) :=
  NLA.Proofs.RE05.selectedCount_charge P hP ε

theorem literal_source_query_bound {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ ω : ℕ → ℝ, ((batchQueries (plans P ε ω)).length : ℝ) ≤
      15 * (2 * Real.sqrt ((q + 1 : ℕ) *
        (16 * Real.log (20 * (q + 1 : ℕ)) + 160 / (ε / 9))) +
        8 * Real.log (20 * (q + 1 : ℕ)) + 1) :=
  NLA.Proofs.RE05.sourceQueryBound P hP ε hε

theorem arbitrary_valid_psd_trace {n : ℕ} (B U V : Square n)
    (sigma : Fin (min n n) → ℝ) (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    (∑ i : Fin n, B i i) =
      ∑ j : Fin n, sigma (Fin.cast (Nat.min_self n).symm j) :=
  NLA.Proofs.RE05.validSVD_posSemidef_trace h hB

theorem actual_zero_singular_sum (n : ℕ) :
    (∑ j : Fin n, (exactSVD (0 : Square n)).sigma
      (Fin.cast (Nat.min_self n).symm j)) = 0 := by
  have h := NLA.Proofs.RE05.exactSVD_posSemidef_trace (0 : Square n)
    (Matrix.PosSemidef.zero)
  simpa using h.symm

/-- Opposite full bases at zero singular values are permitted by the actual
relation; the spectral theorem must not force their equality. -/
theorem zero_opposite_valid (n : ℕ) :
    ValidSVD (0 : Square n) (1 : Square n) (fun _ => 0) (-1 : Square n) := by
  have hI (i j : Fin n) :
      (∑ a : Fin n, (1 : Square n) a i * (1 : Square n) a j) =
        if i = j then 1 else 0 := by simp [Matrix.one_apply, eq_comm]
  refine ⟨hI, ?_, fun _ => le_rfl, fun _ _ _ => le_rfl, ?_⟩
  · intro i j
    simpa only [Matrix.neg_apply, neg_mul_neg] using hI i j
  · intro i j
    simp

theorem zero_opposite_trace (n : ℕ) :
    (0 : Square n).trace =
      ∑ j : Fin n, (fun _ : Fin (min n n) => (0 : ℝ))
        (Fin.cast (Nat.min_self n).symm j) :=
  NLA.Proofs.RE05.validSVD_posSemidef_trace (zero_opposite_valid n) Matrix.PosSemidef.zero

theorem arbitrary_negative_threshold {n : ℕ} (sigma : Fin n → ℝ)
    (hs : ∀ j, 0 ≤ sigma j) :
    (((List.finRange n).filter fun j => (-1 : ℝ) < sigma j).length : ℝ) * (-1) ≤
      ∑ j : Fin n, sigma j := NLA.Proofs.RE05.filter_selected_charge sigma hs (-1)

theorem preserved_full_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel literal_leverage_symmetric
#assert_trust kernel literal_leverage_psd
#assert_trust kernel literal_actual_singular_sum
#assert_trust kernel literal_actual_selected_charge
#assert_trust kernel literal_source_query_bound
#assert_trust kernel arbitrary_valid_psd_trace
#assert_trust kernel actual_zero_singular_sum
#assert_trust kernel zero_opposite_valid
#assert_trust kernel zero_opposite_trace
#assert_trust kernel arbitrary_negative_threshold
#assert_trust kernel preserved_full_target_identity
#print axioms literal_leverage_symmetric
#print axioms literal_leverage_psd
#print axioms literal_actual_singular_sum
#print axioms literal_actual_selected_charge
#print axioms literal_source_query_bound
#print axioms arbitrary_valid_psd_trace
#print axioms actual_zero_singular_sum
#print axioms zero_opposite_valid
#print axioms zero_opposite_trace
#print axioms arbitrary_negative_threshold
#print axioms preserved_full_target_identity
end RE05SpectralGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.leverage_eq_sum_gram
#print axioms NLA.Proofs.RE05.leverage_eq_sum_gram
#assert_trust kernel NLA.Proofs.RE05.leverage_symmetric
#print axioms NLA.Proofs.RE05.leverage_symmetric
#assert_trust kernel NLA.Proofs.RE05.leverage_posSemidef
#print axioms NLA.Proofs.RE05.leverage_posSemidef
#assert_trust kernel NLA.Proofs.RE05.squareSingularValues
#print axioms NLA.Proofs.RE05.squareSingularValues
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_reconstruct
#print axioms NLA.Proofs.RE05.validSVD_square_reconstruct
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_mulVec_right
#print axioms NLA.Proofs.RE05.validSVD_square_mulVec_right
#assert_trust kernel NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left
#print axioms NLA.Proofs.RE05.validSVD_square_transpose_mulVec_left
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_weighted_column
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_weighted_column
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_trace
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_trace
#assert_trust kernel NLA.Proofs.RE05.exactSVD_posSemidef_trace
#print axioms NLA.Proofs.RE05.exactSVD_posSemidef_trace
#assert_trust kernel NLA.Proofs.RE05.exactSVD_leverage_sum
#print axioms NLA.Proofs.RE05.exactSVD_leverage_sum
#assert_trust kernel NLA.Proofs.RE05.filter_selected_charge
#print axioms NLA.Proofs.RE05.filter_selected_charge
#assert_trust kernel NLA.Proofs.RE05.selectedCount_charge
#print axioms NLA.Proofs.RE05.selectedCount_charge
#assert_trust kernel NLA.Proofs.RE05.sourceQueryBound
#print axioms NLA.Proofs.RE05.sourceQueryBound

end
