import NLA.Proofs.RE05.RegressionSolveTransport
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

-- Construct the exact imported private compiler constant as an identifier syntax node.
-- Numeric Name components are not source text identifiers.
open Lean in
macro "private_explicit% " user:str modName:str : term => do
  let decl := Lean.mkPrivateNameCore modName.getString.toName user.getString.toName
  `(@$(Lean.mkIdent decl))
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

#audit_named "NLA.Proofs.RE05.finRange_flatMap_slice" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.planAnswers" "NLA.Proofs.RE05.RegressionTranscript" "public" "definition"

#audit_named "NLA.Proofs.RE05.copyResponses_batchAnswers" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.planAnswers_layout" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.storedVector_append_left" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.storedVector_append_right" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.storedVector_map_get" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.observedLeft_planAnswers" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.observedRight_planAnswers" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.observedLeft_copyResponses" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

#audit_named "NLA.Proofs.RE05.observedRight_copyResponses" "NLA.Proofs.RE05.RegressionTranscript" "public" "theorem"

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

#audit_named "NLA.Proofs.RE05.planFrame" "NLA.Proofs.RE05.ComplementProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.selectedProjection" "NLA.Proofs.RE05.ComplementProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.residualProjection" "NLA.Proofs.RE05.ComplementProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.projection_add_residual" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selectedProjection_symmetric" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualProjection_symmetric" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.complement_eq_mulVec" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.complement_selfAdjoint" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_selected_nodup" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_frame_gram" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selectedProjection_idempotent" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualProjection_idempotent" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_complement_idempotent" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_selectedProjection_idempotent" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualProjection_idempotent" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.projection_basis_split" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selected_residual_mul_zero" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residual_selected_mul_zero" "NLA.Proofs.RE05.ComplementProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.MeasurementIndex" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.MeasurementSpace" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.measurementScale" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.measurementScale_sq" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.packedMeasurement" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.packedMeasurement_inner" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.measurementVector" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.observationVector" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.measurementMap" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.observationVector_planAnswers" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.observationVector_copyResponses" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixRepresentationMap" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.represent_eq_sum" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_single" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientMeasurement" "NLA.Proofs.RE05.MeasurementGeometry" "public" "definition"

#audit_named "NLA.Proofs.RE05.coefficientMeasurement_apply" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientMeasurement_single" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientMeasurement_sum" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_eq_measurement_inner" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.rhs_eq_measurement_inner" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_mulVec_eq_inner" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_quadratic" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.rhs_linear" "NLA.Proofs.RE05.MeasurementGeometry" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.svd_U_gram" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.svd_V_gram" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.svd_U_cogram" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.svd_V_cogram" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.thinU" "NLA.Proofs.RE05.PseudoCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.Pseudo.thinV" "NLA.Proofs.RE05.PseudoCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.Pseudo.sigma" "NLA.Proofs.RE05.PseudoCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.Pseudo.sigmaInv" "NLA.Proofs.RE05.PseudoCore" "public" "definition"

#audit_named "NLA.Proofs.RE05.Pseudo.thinU_orthogonal" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.thinV_orthogonal" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.reconstruction" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.mul_pseudoinverse" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.pseudoinverse_mul" "NLA.Proofs.RE05.PseudoCore" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.IsMP" "NLA.Proofs.RE05.PseudoIdentities" "public" "definition"

#audit_named "NLA.Proofs.RE05.Pseudo.sandwich_contract" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.Pseudo.actual_isMP" "NLA.Proofs.RE05.PseudoIdentities" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_hermitian" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_posSemidef" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.regression_quadratic" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_normal_coefficients" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_normal" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.normal_measurement_orthogonal" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.normal_pythagorean" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_minimizes" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_batch_normal" "NLA.Proofs.RE05.RegressionNormal" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_mem_span_iff" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_mem_span" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_injective" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_represent_sum" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalCoordinates" "NLA.Proofs.RE05.RegressionBasis" "public" "definition"

#audit_named "NLA.Proofs.RE05.orthonormalCoordinates_represent" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_in_orthonormal_span" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormal_represent_in_supplied_span" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalCoordinates_reconstruct" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormal_representation_inner" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormalCoordinates_inner" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_orthonormal_transport" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.rhs_orthonormal_transport" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.OrthonormalMeasurementLowerBound" "NLA.Proofs.RE05.RegressionBasis" "public" "definition"

#audit_named "NLA.Proofs.RE05.measurement_lower_bound_supplied" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_posDef_of_lower_bound" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gram_full_rank_of_lower_bound" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_unique_of_lower_bound" "NLA.Proofs.RE05.RegressionBasis" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormal_solve_supplied_normal" "NLA.Proofs.RE05.RegressionSolveTransport" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound" "NLA.Proofs.RE05.RegressionSolveTransport" "public" "theorem"

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
example {α : Type*} {m : ℕ} (f : Fin m → List α) (j : Fin m) :
    (((List.finRange m).flatMap f).drop
      (∑ i : Fin m, if i < j then (f i).length else 0)).take (f j).length = f j := by
  exact @NLA.Proofs.RE05.finRange_flatMap_slice α m f j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) :
    copyResponses schedule (batchAnswers A schedule) copy = planAnswers A (schedule copy) := by
  exact @NLA.Proofs.RE05.copyResponses_batchAnswers n A schedule copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (plan : Plan n) :
    planAnswers A plan =
      plan.selected.map (fun h => fun k => ∑ i : Fin n, A i k * plan.U i h) ++
        (List.finRange plan.s).map (fun g => fun i => ∑ k : Fin n, A i k * plan.G k g) := by
  exact @NLA.Proofs.RE05.planAnswers_layout n A plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (xs ys : List (Fin n → ℝ)) (j : ℕ)
    (hj : j < xs.length) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs ++ ys) j =
      NLA.Computation.NonadaptiveMatrixQuery.storedVector xs j := by
  exact @NLA.Proofs.RE05.storedVector_append_left n xs ys j hj
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (xs ys : List (Fin n → ℝ)) (j : ℕ) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs ++ ys) (xs.length + j) =
      NLA.Computation.NonadaptiveMatrixQuery.storedVector ys j := by
  exact @NLA.Proofs.RE05.storedVector_append_right n xs ys j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {α : Type*} {n : ℕ} (xs : List α)
    (f : α → Fin n → ℝ) (j : Fin xs.length) :
    NLA.Computation.NonadaptiveMatrixQuery.storedVector (xs.map f) j.val = f xs[j] := by
  exact @NLA.Proofs.RE05.storedVector_map_get α n xs f j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (plan : Plan n)
    (h : Fin plan.selected.length) :
    observedLeft plan (planAnswers A plan) h = A.transpose *ᵥ uColumn plan h := by
  exact @NLA.Proofs.RE05.observedLeft_planAnswers n A plan h
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (plan : Plan n)
    (g : Fin plan.s) :
    observedRight plan (planAnswers A plan) g = A *ᵥ (fun k => plan.G k g) := by
  exact @NLA.Proofs.RE05.observedRight_planAnswers n A plan g
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) (h : Fin (schedule copy).selected.length) :
    observedLeft (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) h =
      A.transpose *ᵥ uColumn (schedule copy) h := by
  exact @NLA.Proofs.RE05.observedLeft_copyResponses n A schedule copy h
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) (g : Fin (schedule copy).s) :
    observedRight (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) g =
      A *ᵥ (fun k => (schedule copy).G k g) := by
  exact @NLA.Proofs.RE05.observedRight_copyResponses n A schedule copy g
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) :
    measurementScale plan ^ 2 = 1 / (plan.s : ℝ) := by
  exact @NLA.Proofs.RE05.measurementScale_sq n plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (L L' : Fin plan.selected.length → Fin n → ℝ)
    (R R' : Fin plan.s → Fin n → ℝ) :
    ⟪packedMeasurement plan L R, packedMeasurement plan L' R'⟫_ℝ =
      (∑ h, dot (L h) (L' h)) + (1 / (plan.s : ℝ)) * ∑ g, dot (R g) (R' g) := by
  exact @NLA.Proofs.RE05.packedMeasurement_inner n plan L L' R R'
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) (plan : Plan n) :
    observationVector plan (planAnswers A plan) = measurementVector plan A := by
  exact @NLA.Proofs.RE05.observationVector_planAnswers n A plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) :
    observationVector (schedule copy) (copyResponses schedule (batchAnswers A schedule) copy) =
      measurementVector (schedule copy) A := by
  exact @NLA.Proofs.RE05.observationVector_copyResponses n A schedule copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    represent P c = ∑ j, c j • P j := by
  exact @NLA.Proofs.RE05.represent_eq_sum n q P c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (j : Fin (q + 1)) :
    represent P (Pi.single j 1) = P j := by
  exact @NLA.Proofs.RE05.represent_single n q P j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    coefficientMeasurement P plan c = measurementVector plan (represent P c) := by
  exact @NLA.Proofs.RE05.coefficientMeasurement_apply n q P plan c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (j : Fin (q + 1)) :
    coefficientMeasurement P plan (Pi.single j 1) = measurementVector plan (P j) := by
  exact @NLA.Proofs.RE05.coefficientMeasurement_single n q P plan j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    coefficientMeasurement P plan c = ∑ j, c j • measurementVector plan (P j) := by
  exact @NLA.Proofs.RE05.coefficientMeasurement_sum n q P plan c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (j k : Fin (q + 1)) :
    gram P plan j k = ⟪measurementVector plan (P j), measurementVector plan (P k)⟫_ℝ := by
  exact @NLA.Proofs.RE05.gram_eq_measurement_inner n q P plan j k
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    rhs P plan responses j = ⟪measurementVector plan (P j), observationVector plan responses⟫_ℝ := by
  exact @NLA.Proofs.RE05.rhs_eq_measurement_inner n q P plan responses j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) (j : Fin (q + 1)) :
    (gram P plan *ᵥ c) j =
      ⟪measurementVector plan (P j), coefficientMeasurement P plan c⟫_ℝ := by
  exact @NLA.Proofs.RE05.gram_mulVec_eq_inner n q P plan c j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c d : Fin (q + 1) → ℝ) :
    dot c (gram P plan *ᵥ d) =
      ⟪coefficientMeasurement P plan c, coefficientMeasurement P plan d⟫_ℝ := by
  exact @NLA.Proofs.RE05.gram_quadratic n q P plan c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    dot c (rhs P plan responses) =
      ⟪coefficientMeasurement P plan c, observationVector plan responses⟫_ℝ := by
  exact @NLA.Proofs.RE05.rhs_linear n q P plan responses c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (exactSVD B).U.transpose * (exactSVD B).U = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.svd_U_gram a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (exactSVD B).V.transpose * (exactSVD B).V = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.svd_V_gram a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (exactSVD B).U * (exactSVD B).U.transpose = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.svd_U_cogram a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (exactSVD B).V * (exactSVD B).V.transpose = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.svd_V_cogram a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (thinU B).transpose * thinU B = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.thinU_orthogonal a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (thinV B).transpose * thinV B = 1 := by
  exact @NLA.Proofs.RE05.Pseudo.thinV_orthogonal a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B = thinU B * Matrix.diagonal (sigma B) * (thinV B).transpose := by
  exact @NLA.Proofs.RE05.Pseudo.reconstruction a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B = thinV B * Matrix.diagonal (sigmaInv B) * (thinU B).transpose := by
  exact @NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) =
      Matrix.diagonal (sigma B) := by
  exact @NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) =
      Matrix.diagonal (sigmaInv B) := by
  exact @NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B) =
      Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B) := by
  exact @NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B * pseudoInverse B = thinU B *
      (Matrix.diagonal (sigma B) * Matrix.diagonal (sigmaInv B)) * (thinU B).transpose := by
  exact @NLA.Proofs.RE05.Pseudo.mul_pseudoinverse a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B * B = thinV B *
      (Matrix.diagonal (sigmaInv B) * Matrix.diagonal (sigma B)) * (thinV B).transpose := by
  exact @NLA.Proofs.RE05.Pseudo.pseudoinverse_mul a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b t : ℕ} (U : Matrix (Fin a) (Fin t) ℝ)
    (hU : U.transpose * U = 1) (D E : Matrix (Fin t) (Fin t) ℝ)
    (W : Matrix (Fin t) (Fin b) ℝ) :
    (U * D * U.transpose) * (U * E * W) = U * (D * E) * W := by
  exact @NLA.Proofs.RE05.Pseudo.sandwich_contract a b t U hU D E W
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a t : ℕ} (U : Matrix (Fin a) (Fin t) ℝ)
    (d : Fin t → ℝ) :
    (U * Matrix.diagonal d * U.transpose).transpose = U * Matrix.diagonal d * U.transpose := by
  exact @NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose a t U d
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    B * pseudoInverse B * B = B := by
  exact @NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    pseudoInverse B * B * pseudoInverse B = pseudoInverse B := by
  exact @NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (B * pseudoInverse B).transpose = B * pseudoInverse B := by
  exact @NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    (pseudoInverse B * B).transpose = pseudoInverse B * B := by
  exact @NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05.Pseudo
open NLA.Computation.NonadaptiveMatrixQuery
example {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    IsMP B (pseudoInverse B) := by
  exact @NLA.Proofs.RE05.Pseudo.actual_isMP a b B
end NLA.Proofs.RE05.Pseudo
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (gram P plan).IsHermitian := by
  exact @NLA.Proofs.RE05.gram_hermitian n q P plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (gram P plan).PosSemidef := by
  exact @NLA.Proofs.RE05.gram_posSemidef n q P plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan c‖ ^ 2 =
      ‖observationVector plan responses‖ ^ 2 - 2 * dot c (rhs P plan responses) +
        dot c (gram P plan *ᵥ c) := by
  exact @NLA.Proofs.RE05.regression_quadratic n q P plan responses c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    ∃ c : Fin (q + 1) → ℝ, gram P plan *ᵥ c = rhs P plan responses := by
  exact @NLA.Proofs.RE05.exists_normal_coefficients n q P plan responses
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    singleOutput P plan responses =
      NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse (gram P plan) *ᵥ
        rhs P plan responses := by
  exact @NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec n q P plan responses
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) :
    gram P plan *ᵥ singleOutput P plan responses = rhs P plan responses := by
  exact @NLA.Proofs.RE05.singleOutput_normal n q P plan responses
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ)
    (hc : gram P plan *ᵥ c = rhs P plan responses) (d : Fin (q + 1) → ℝ) :
    ⟪observationVector plan responses - coefficientMeasurement P plan c,
      coefficientMeasurement P plan d⟫_ℝ = 0 := by
  exact @NLA.Proofs.RE05.normal_measurement_orthogonal n q P plan responses c hc d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ)
    (hc : gram P plan *ᵥ c = rhs P plan responses) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan d‖ ^ 2 =
      ‖observationVector plan responses - coefficientMeasurement P plan c‖ ^ 2 +
      ‖coefficientMeasurement P plan c - coefficientMeasurement P plan d‖ ^ 2 := by
  exact @NLA.Proofs.RE05.normal_pythagorean n q P plan responses c hc d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (responses : List (Fin n → ℝ)) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan responses - coefficientMeasurement P plan
      (singleOutput P plan responses)‖ ^ 2 ≤
      ‖observationVector plan responses - coefficientMeasurement P plan d‖ ^ 2 := by
  exact @NLA.Proofs.RE05.singleOutput_minimizes n q P plan responses d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (A : Square n)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) (j : Fin (q + 1)) :
    ⟪measurementVector (schedule copy) (P j),
      measurementVector (schedule copy)
        (A - represent P (singleOutput P (schedule copy)
          (copyResponses schedule (batchAnswers A schedule) copy)))⟫_ℝ = 0 := by
  exact @NLA.Proofs.RE05.singleOutput_batch_normal n q P A schedule copy j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (M : Square n) :
    M ∈ Submodule.span ℝ (Set.range P) ↔ ∃ c, represent P c = M := by
  exact @NLA.Proofs.RE05.represent_mem_span_iff n q P M
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    represent P c ∈ Submodule.span ℝ (Set.range P) := by
  exact @NLA.Proofs.RE05.represent_mem_span n q P c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P) :
    Function.Injective (represent P) := by
  exact @NLA.Proofs.RE05.represent_injective n q P hP
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (c : Fin (q + 1) → ℝ) :
    matrixVector (represent P c) = ∑ j, c j • matrixVector (P j) := by
  exact @NLA.Proofs.RE05.matrixVector_represent_sum n q P c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (d : Fin (q + 1) → ℝ) :
    orthonormalCoordinates P (represent (orthonormalMember P) d) = d := by
  exact @NLA.Proofs.RE05.orthonormalCoordinates_represent n q P hP d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (c : Fin (q + 1) → ℝ) :
    ∃ d, represent (orthonormalMember P) d = represent P c := by
  exact @NLA.Proofs.RE05.represent_in_orthonormal_span n q P hP c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (d : Fin (q + 1) → ℝ) :
    ∃ c, represent P c = represent (orthonormalMember P) d := by
  exact @NLA.Proofs.RE05.orthonormal_represent_in_supplied_span n q P hP d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (M : Square n) (hM : M ∈ Submodule.span ℝ (Set.range P)) :
    represent (orthonormalMember P) (orthonormalCoordinates P M) = M := by
  exact @NLA.Proofs.RE05.orthonormalCoordinates_reconstruct n q P hP M hM
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (c d : Fin (q + 1) → ℝ) :
    NLA.Computation.LinearFamilyQuery.inner (represent (orthonormalMember P) c)
      (represent (orthonormalMember P) d) = dot c d := by
  exact @NLA.Proofs.RE05.orthonormal_representation_inner n q P hP c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (M N : Square n) (hM : M ∈ Submodule.span ℝ (Set.range P))
    (hN : N ∈ Submodule.span ℝ (Set.range P)) :
    dot (orthonormalCoordinates P M) (orthonormalCoordinates P N) =
      NLA.Computation.LinearFamilyQuery.inner M N := by
  exact @NLA.Proofs.RE05.orthonormalCoordinates_inner n q P hP M N hM hN
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (c d : Fin (q + 1) → ℝ) :
    dot c (gram P plan *ᵥ d) =
      dot (orthonormalCoordinates P (represent P c))
        (gram (orthonormalMember P) plan *ᵥ orthonormalCoordinates P (represent P d)) := by
  exact @NLA.Proofs.RE05.gram_orthonormal_transport n q P hP plan c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (responses : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    dot c (rhs P plan responses) =
      dot (orthonormalCoordinates P (represent P c))
        (rhs (orthonormalMember P) plan responses) := by
  exact @NLA.Proofs.RE05.rhs_orthonormal_transport n q P hP plan responses c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (α : ℝ)
    (hLower : OrthonormalMeasurementLowerBound P plan α) (c : Fin (q + 1) → ℝ) :
    α * NLA.Computation.LinearFamilyQuery.inner (represent P c) (represent P c) ≤
      dot c (gram P plan *ᵥ c) := by
  exact @NLA.Proofs.RE05.measurement_lower_bound_supplied n q P hP plan α hLower c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : OrthonormalMeasurementLowerBound P plan α) : (gram P plan).PosDef := by
  exact @NLA.Proofs.RE05.gram_posDef_of_lower_bound n q P hP plan α hα hLower
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : OrthonormalMeasurementLowerBound P plan α) :
    Matrix.rank (gram P plan) = q + 1 := by
  exact @NLA.Proofs.RE05.gram_full_rank_of_lower_bound n q P hP plan α hα hLower
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α)
    (c : Fin (q + 1) → ℝ) (hc : gram P plan *ᵥ c = rhs P plan responses) :
    c = singleOutput P plan responses := by
  exact @NLA.Proofs.RE05.singleOutput_unique_of_lower_bound n q P hP plan responses α hα hLower c hc
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (c : Fin (q + 1) → ℝ)
    (hc : represent P c = represent (orthonormalMember P)
      (singleOutput (orthonormalMember P) plan responses)) :
    gram P plan *ᵥ c = rhs P plan responses := by
  exact @NLA.Proofs.RE05.orthonormal_solve_supplied_normal n q P hP plan responses c hc
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α) :
    represent P (singleOutput P plan responses) =
      represent (orthonormalMember P) (singleOutput (orthonormalMember P) plan responses) := by
  exact @NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound n q P hP plan responses α hα hLower
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05RegressionGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix InnerProductSpace

theorem literal_response_slice {n : ℕ} (A : Square n) (schedule : Fin 15 → Plan n)
    (copy : Fin 15) :
    copyResponses schedule (batchAnswers A schedule) copy =
      (queries (schedule copy)).map (NLA.Computation.NonadaptiveMatrixQuery.answer A) :=
  copyResponses_batchAnswers A schedule copy

theorem literal_left_answer {n q : ℕ} (P : Basis n q) (A : Square n) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (h : Fin (plans P ε ω copy).selected.length) :
    observedLeft (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy) h =
      A.transpose *ᵥ uColumn (plans P ε ω copy) h :=
  observedLeft_copyResponses A (plans P ε ω) copy h

theorem literal_right_answer {n q : ℕ} (P : Basis n q) (A : Square n) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (g : Fin (plans P ε ω copy).s) :
    observedRight (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy) g =
      A *ᵥ (fun k => (plans P ε ω copy).G k g) :=
  observedRight_copyResponses A (plans P ε ω) copy g

theorem literal_mp_entry {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    singleOutput P plan R j = ∑ k,
      NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse (gram P plan) j k * rhs P plan R k := rfl

theorem literal_original_normal_entry {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (j : Fin (q + 1)) :
    (∑ k, gram P plan j k * singleOutput P plan R k) = rhs P plan R j :=
  congrFun (singleOutput_normal P plan R) j

theorem literal_measured_quadratic {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (c : Fin (q + 1) → ℝ) :
    ‖observationVector plan R - measurementVector plan (represent P c)‖ ^ 2 =
      ‖observationVector plan R‖ ^ 2 - 2 * dot c (rhs P plan R) + dot c (gram P plan *ᵥ c) :=
  regression_quadratic P plan R c

theorem literal_original_minimum {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : List (Fin n → ℝ)) (d : Fin (q + 1) → ℝ) :
    ‖observationVector plan R - measurementVector plan (represent P (singleOutput P plan R))‖ ^ 2 ≤
      ‖observationVector plan R - measurementVector plan (represent P d)‖ ^ 2 :=
  singleOutput_minimizes P plan R d

theorem literal_actual_basis_reconstruction {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (c : Fin (q + 1) → ℝ) :
    represent (orthonormalMember P)
      (fun j => NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) (represent P c)) =
      represent P c :=
  orthonormalCoordinates_reconstruct P hP _ (represent_mem_span P c)

theorem literal_lower_event_full_rank {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ,
      α * dot d d ≤ dot d (gram (orthonormalMember P) plan *ᵥ d)) :
    Matrix.rank (gram P plan) = q + 1 :=
  gram_full_rank_of_lower_bound P hP plan α hα hLower

theorem literal_conditional_matrix_output {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (plan : Plan n) (R : List (Fin n → ℝ)) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ,
      α * dot d d ≤ dot d (gram (orthonormalMember P) plan *ᵥ d)) :
    represent P (singleOutput P plan R) =
      represent (orthonormalMember P) (singleOutput (orthonormalMember P) plan R) :=
  singleOutput_matrix_basis_invariant_of_lower_bound P hP plan R α hα hLower

/-- No selected columns, zero sketch width and dependent generators are
allowed by the unconditional solve, for any actual response list. -/
theorem zero_width_dependent_output {n q : ℕ} (P : Basis n q) (U : Square n)
    (G : Matrix (Fin n) (Fin 0) ℝ) (R : List (Fin n → ℝ)) :
    singleOutput P ⟨[], U, 0, G⟩ R = 0 := by
  rw [singleOutput_eq_pseudoInverse_mulVec]
  have hb : rhs P ⟨[], U, 0, G⟩ R = 0 := by ext j; simp [rhs]
  rw [hb, Matrix.mulVec_zero]

theorem empty_matrix_normal (q : ℕ) (P : Basis 0 q) (plan : Plan 0)
    (R : List (Fin 0 → ℝ)) :
    gram P plan *ᵥ singleOutput P plan R = rhs P plan R := singleOutput_normal P plan R

theorem actual_rectangular_mp (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ) :
    B * NLA.Computation.NonadaptiveMatrixQuery.pseudoInverse B * B = B :=
  Pseudo.mul_pseudoinverse_mul B

end RE05RegressionGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_U_gram
#print axioms NLA.Proofs.RE05.Pseudo.svd_U_gram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_V_gram
#print axioms NLA.Proofs.RE05.Pseudo.svd_V_gram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_U_cogram
#print axioms NLA.Proofs.RE05.Pseudo.svd_U_cogram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.svd_V_cogram
#print axioms NLA.Proofs.RE05.Pseudo.svd_V_cogram
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinU
#print axioms NLA.Proofs.RE05.Pseudo.thinU
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinV
#print axioms NLA.Proofs.RE05.Pseudo.thinV
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sigma
#print axioms NLA.Proofs.RE05.Pseudo.sigma
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sigmaInv
#print axioms NLA.Proofs.RE05.Pseudo.sigmaInv
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinU_orthogonal
#print axioms NLA.Proofs.RE05.Pseudo.thinU_orthogonal
#assert_trust kernel NLA.Proofs.RE05.Pseudo.thinV_orthogonal
#print axioms NLA.Proofs.RE05.Pseudo.thinV_orthogonal
#assert_trust kernel NLA.Proofs.RE05.Pseudo.reconstruction
#print axioms NLA.Proofs.RE05.Pseudo.reconstruction
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_decomposition
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_sigma
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_inv_sigma_inv
#assert_trust kernel NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute
#print axioms NLA.Proofs.RE05.Pseudo.diagonal_sigma_inv_commute
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE05.Pseudo.IsMP
#print axioms NLA.Proofs.RE05.Pseudo.IsMP
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sandwich_contract
#print axioms NLA.Proofs.RE05.Pseudo.sandwich_contract
#assert_trust kernel NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose
#print axioms NLA.Proofs.RE05.Pseudo.sandwich_diagonal_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_mul
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_pseudoinverse
#assert_trust kernel NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose
#print axioms NLA.Proofs.RE05.Pseudo.mul_pseudoinverse_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose
#print axioms NLA.Proofs.RE05.Pseudo.pseudoinverse_mul_transpose
#assert_trust kernel NLA.Proofs.RE05.Pseudo.actual_isMP
#print axioms NLA.Proofs.RE05.Pseudo.actual_isMP
#assert_trust kernel NLA.Proofs.RE05.finRange_flatMap_slice
#print axioms NLA.Proofs.RE05.finRange_flatMap_slice
#assert_trust kernel NLA.Proofs.RE05.planAnswers
#print axioms NLA.Proofs.RE05.planAnswers
#assert_trust kernel NLA.Proofs.RE05.copyResponses_batchAnswers
#print axioms NLA.Proofs.RE05.copyResponses_batchAnswers
#assert_trust kernel NLA.Proofs.RE05.planAnswers_layout
#print axioms NLA.Proofs.RE05.planAnswers_layout
#assert_trust kernel NLA.Proofs.RE05.storedVector_append_left
#print axioms NLA.Proofs.RE05.storedVector_append_left
#assert_trust kernel NLA.Proofs.RE05.storedVector_append_right
#print axioms NLA.Proofs.RE05.storedVector_append_right
#assert_trust kernel NLA.Proofs.RE05.storedVector_map_get
#print axioms NLA.Proofs.RE05.storedVector_map_get
#assert_trust kernel NLA.Proofs.RE05.observedLeft_planAnswers
#print axioms NLA.Proofs.RE05.observedLeft_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observedRight_planAnswers
#print axioms NLA.Proofs.RE05.observedRight_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observedLeft_copyResponses
#print axioms NLA.Proofs.RE05.observedLeft_copyResponses
#assert_trust kernel NLA.Proofs.RE05.observedRight_copyResponses
#print axioms NLA.Proofs.RE05.observedRight_copyResponses
#assert_trust kernel NLA.Proofs.RE05.MeasurementIndex
#print axioms NLA.Proofs.RE05.MeasurementIndex
#assert_trust kernel NLA.Proofs.RE05.MeasurementSpace
#print axioms NLA.Proofs.RE05.MeasurementSpace
#assert_trust kernel NLA.Proofs.RE05.measurementScale
#print axioms NLA.Proofs.RE05.measurementScale
#assert_trust kernel NLA.Proofs.RE05.measurementScale_sq
#print axioms NLA.Proofs.RE05.measurementScale_sq
#assert_trust kernel NLA.Proofs.RE05.packedMeasurement
#print axioms NLA.Proofs.RE05.packedMeasurement
#assert_trust kernel NLA.Proofs.RE05.packedMeasurement_inner
#print axioms NLA.Proofs.RE05.packedMeasurement_inner
#assert_trust kernel NLA.Proofs.RE05.measurementVector
#print axioms NLA.Proofs.RE05.measurementVector
#assert_trust kernel NLA.Proofs.RE05.observationVector
#print axioms NLA.Proofs.RE05.observationVector
#assert_trust kernel NLA.Proofs.RE05.measurementMap
#print axioms NLA.Proofs.RE05.measurementMap
#assert_trust kernel NLA.Proofs.RE05.observationVector_planAnswers
#print axioms NLA.Proofs.RE05.observationVector_planAnswers
#assert_trust kernel NLA.Proofs.RE05.observationVector_copyResponses
#print axioms NLA.Proofs.RE05.observationVector_copyResponses
#assert_trust kernel NLA.Proofs.RE05.matrixRepresentationMap
#print axioms NLA.Proofs.RE05.matrixRepresentationMap
#assert_trust kernel NLA.Proofs.RE05.represent_eq_sum
#print axioms NLA.Proofs.RE05.represent_eq_sum
#assert_trust kernel NLA.Proofs.RE05.represent_single
#print axioms NLA.Proofs.RE05.represent_single
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement
#print axioms NLA.Proofs.RE05.coefficientMeasurement
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_apply
#print axioms NLA.Proofs.RE05.coefficientMeasurement_apply
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_single
#print axioms NLA.Proofs.RE05.coefficientMeasurement_single
#assert_trust kernel NLA.Proofs.RE05.coefficientMeasurement_sum
#print axioms NLA.Proofs.RE05.coefficientMeasurement_sum
#assert_trust kernel NLA.Proofs.RE05.gram_eq_measurement_inner
#print axioms NLA.Proofs.RE05.gram_eq_measurement_inner
#assert_trust kernel NLA.Proofs.RE05.rhs_eq_measurement_inner
#print axioms NLA.Proofs.RE05.rhs_eq_measurement_inner
#assert_trust kernel NLA.Proofs.RE05.gram_mulVec_eq_inner
#print axioms NLA.Proofs.RE05.gram_mulVec_eq_inner
#assert_trust kernel NLA.Proofs.RE05.gram_quadratic
#print axioms NLA.Proofs.RE05.gram_quadratic
#assert_trust kernel NLA.Proofs.RE05.rhs_linear
#print axioms NLA.Proofs.RE05.rhs_linear
#assert_trust kernel NLA.Proofs.RE05.gram_hermitian
#print axioms NLA.Proofs.RE05.gram_hermitian
#assert_trust kernel NLA.Proofs.RE05.gram_posSemidef
#print axioms NLA.Proofs.RE05.gram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.regression_quadratic
#print axioms NLA.Proofs.RE05.regression_quadratic
#assert_trust kernel NLA.Proofs.RE05.exists_normal_coefficients
#print axioms NLA.Proofs.RE05.exists_normal_coefficients
#assert_trust kernel NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec
#print axioms NLA.Proofs.RE05.singleOutput_eq_pseudoInverse_mulVec
#assert_trust kernel NLA.Proofs.RE05.singleOutput_normal
#print axioms NLA.Proofs.RE05.singleOutput_normal
#assert_trust kernel NLA.Proofs.RE05.normal_measurement_orthogonal
#print axioms NLA.Proofs.RE05.normal_measurement_orthogonal
#assert_trust kernel NLA.Proofs.RE05.normal_pythagorean
#print axioms NLA.Proofs.RE05.normal_pythagorean
#assert_trust kernel NLA.Proofs.RE05.singleOutput_minimizes
#print axioms NLA.Proofs.RE05.singleOutput_minimizes
#assert_trust kernel NLA.Proofs.RE05.singleOutput_batch_normal
#print axioms NLA.Proofs.RE05.singleOutput_batch_normal
#assert_trust kernel NLA.Proofs.RE05.represent_mem_span_iff
#print axioms NLA.Proofs.RE05.represent_mem_span_iff
#assert_trust kernel NLA.Proofs.RE05.represent_mem_span
#print axioms NLA.Proofs.RE05.represent_mem_span
#assert_trust kernel NLA.Proofs.RE05.represent_injective
#print axioms NLA.Proofs.RE05.represent_injective
#assert_trust kernel NLA.Proofs.RE05.matrixVector_represent_sum
#print axioms NLA.Proofs.RE05.matrixVector_represent_sum
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates
#print axioms NLA.Proofs.RE05.orthonormalCoordinates
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_represent
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_represent
#assert_trust kernel NLA.Proofs.RE05.represent_in_orthonormal_span
#print axioms NLA.Proofs.RE05.represent_in_orthonormal_span
#assert_trust kernel NLA.Proofs.RE05.orthonormal_represent_in_supplied_span
#print axioms NLA.Proofs.RE05.orthonormal_represent_in_supplied_span
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_reconstruct
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_reconstruct
#assert_trust kernel NLA.Proofs.RE05.orthonormal_representation_inner
#print axioms NLA.Proofs.RE05.orthonormal_representation_inner
#assert_trust kernel NLA.Proofs.RE05.orthonormalCoordinates_inner
#print axioms NLA.Proofs.RE05.orthonormalCoordinates_inner
#assert_trust kernel NLA.Proofs.RE05.gram_orthonormal_transport
#print axioms NLA.Proofs.RE05.gram_orthonormal_transport
#assert_trust kernel NLA.Proofs.RE05.rhs_orthonormal_transport
#print axioms NLA.Proofs.RE05.rhs_orthonormal_transport
#assert_trust kernel NLA.Proofs.RE05.OrthonormalMeasurementLowerBound
#print axioms NLA.Proofs.RE05.OrthonormalMeasurementLowerBound
#assert_trust kernel NLA.Proofs.RE05.measurement_lower_bound_supplied
#print axioms NLA.Proofs.RE05.measurement_lower_bound_supplied
#assert_trust kernel NLA.Proofs.RE05.gram_posDef_of_lower_bound
#print axioms NLA.Proofs.RE05.gram_posDef_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.gram_full_rank_of_lower_bound
#print axioms NLA.Proofs.RE05.gram_full_rank_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.singleOutput_unique_of_lower_bound
#print axioms NLA.Proofs.RE05.singleOutput_unique_of_lower_bound
#assert_trust kernel NLA.Proofs.RE05.orthonormal_solve_supplied_normal
#print axioms NLA.Proofs.RE05.orthonormal_solve_supplied_normal
#assert_trust kernel NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound
#print axioms NLA.Proofs.RE05.singleOutput_matrix_basis_invariant_of_lower_bound
#assert_trust kernel RE05RegressionGeometryConsumer.literal_response_slice
#print axioms RE05RegressionGeometryConsumer.literal_response_slice
#assert_trust kernel RE05RegressionGeometryConsumer.literal_left_answer
#print axioms RE05RegressionGeometryConsumer.literal_left_answer
#assert_trust kernel RE05RegressionGeometryConsumer.literal_right_answer
#print axioms RE05RegressionGeometryConsumer.literal_right_answer
#assert_trust kernel RE05RegressionGeometryConsumer.literal_mp_entry
#print axioms RE05RegressionGeometryConsumer.literal_mp_entry
#assert_trust kernel RE05RegressionGeometryConsumer.literal_original_normal_entry
#print axioms RE05RegressionGeometryConsumer.literal_original_normal_entry
#assert_trust kernel RE05RegressionGeometryConsumer.literal_measured_quadratic
#print axioms RE05RegressionGeometryConsumer.literal_measured_quadratic
#assert_trust kernel RE05RegressionGeometryConsumer.literal_original_minimum
#print axioms RE05RegressionGeometryConsumer.literal_original_minimum
#assert_trust kernel RE05RegressionGeometryConsumer.literal_actual_basis_reconstruction
#print axioms RE05RegressionGeometryConsumer.literal_actual_basis_reconstruction
#assert_trust kernel RE05RegressionGeometryConsumer.literal_lower_event_full_rank
#print axioms RE05RegressionGeometryConsumer.literal_lower_event_full_rank
#assert_trust kernel RE05RegressionGeometryConsumer.literal_conditional_matrix_output
#print axioms RE05RegressionGeometryConsumer.literal_conditional_matrix_output
#assert_trust kernel RE05RegressionGeometryConsumer.zero_width_dependent_output
#print axioms RE05RegressionGeometryConsumer.zero_width_dependent_output
#assert_trust kernel RE05RegressionGeometryConsumer.empty_matrix_normal
#print axioms RE05RegressionGeometryConsumer.empty_matrix_normal
#assert_trust kernel RE05RegressionGeometryConsumer.actual_rectangular_mp
#print axioms RE05RegressionGeometryConsumer.actual_rectangular_mp

end
