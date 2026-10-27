import NLA.Proofs.RE05.OffsetContraction
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

#audit_named "NLA.Proofs.RE05.regressionOffset" "NLA.Proofs.RE05.RegressionOffset" "public" "definition"

#audit_named "NLA.Proofs.RE05.regressionOffset_inner" "NLA.Proofs.RE05.RegressionOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.regressionOffset_sub" "NLA.Proofs.RE05.RegressionOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.regressionOffset_represent" "NLA.Proofs.RE05.RegressionOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_residual_equation" "NLA.Proofs.RE05.RegressionOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_batch_residual_equation" "NLA.Proofs.RE05.RegressionOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_posSemidef_positive_column" "NLA.Proofs.RE05.PositiveSVDColumns" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry" "NLA.Proofs.RE05.PositiveSVDColumns" "public" "theorem"

#audit_named "NLA.Proofs.RE05.validSVD_posSemidef_diagonalization" "NLA.Proofs.RE05.PositiveSVDColumns" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverageFrame" "NLA.Proofs.RE05.LeverageMask" "public" "definition"

#audit_named "NLA.Proofs.RE05.leverageSingularValues" "NLA.Proofs.RE05.LeverageMask" "public" "definition"

#audit_named "NLA.Proofs.RE05.selectedMask" "NLA.Proofs.RE05.LeverageMask" "public" "definition"

#audit_named "NLA.Proofs.RE05.residualMask" "NLA.Proofs.RE05.LeverageMask" "public" "definition"

#audit_named "NLA.Proofs.RE05.validSVD_left_gram" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverageFrame_gram" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverageFrame_cogram" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frame_conjugate_mul" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_sum_selected" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_selectedProjection_mask" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualMask_diagonal" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualProjection_mask" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.leverage_diagonalization" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualProjection_posSemidef" "NLA.Proofs.RE05.LeverageMask" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualSingularValues" "NLA.Proofs.RE05.ResidualLeverage" "public" "definition"

#audit_named "NLA.Proofs.RE05.residualMask_spectrum" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualSingularValues_le_threshold" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frame_constant_diagonal" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualLeverage_bound" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualLeverage_quadratic" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualBasisBlock" "NLA.Proofs.RE05.ResidualLeverage" "public" "definition"

#audit_named "NLA.Proofs.RE05.residualBasisBlock_gram" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actual_basis_split" "NLA.Proofs.RE05.ResidualLeverage" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrix_inner_trace" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrix_inner_comm" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrix_inner_add_left" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrix_inner_add_right" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrix_inner_self_nonnegative" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.projection_matrix_inner_cross" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.projection_matrix_inner_split" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixFamilyGram" "NLA.Proofs.RE05.BasisProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.matrixFamilyGram_posSemidef" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.selectedBasisGram" "NLA.Proofs.RE05.BasisProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.residualBasisGram" "NLA.Proofs.RE05.BasisProjection" "public" "definition"

#audit_named "NLA.Proofs.RE05.selectedBasisGram_posSemidef" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.residualBasisGram_posSemidef" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_basisGram_split" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_residualBasisGram_le_one" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one" "NLA.Proofs.RE05.BasisProjection" "public" "theorem"

#audit_named "NLA.Proofs.RE05.measuredLeft_eq_trace" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.measuredLeft_inner_selected" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.measuredLeft_inner_projection" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.dot_mulVec_quadratic" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.dot_quadratic_eq_sum" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.offsetQuadraticMatrix" "NLA.Proofs.RE05.CenteredOffset" "public" "definition"

#audit_named "NLA.Proofs.RE05.makePlan_residualProjection_eq" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.offsetQuadraticMatrix_trace" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actualResidualOffset_centered_unscaled" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussianWidth_positive" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actualResidualOffset_centered" "NLA.Proofs.RE05.CenteredOffset" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection" "NLA.Proofs.RE05.OffsetContraction" "public" "theorem"

#audit_named "NLA.Proofs.RE05.family_transpose_product_energy" "NLA.Proofs.RE05.OffsetContraction" "public" "theorem"

#audit_named "NLA.Proofs.RE05.scalar_psd_trace_bound" "NLA.Proofs.RE05.OffsetContraction" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction" "NLA.Proofs.RE05.OffsetContraction" "public" "theorem"

#audit_named "NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge" "NLA.Proofs.RE05.OffsetContraction" "public" "theorem"

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
example {n : ℕ} (plan : Plan n) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      (((B.transpose * planFrame plan).transpose) * (A.transpose * planFrame plan)).trace := by
  exact @NLA.Proofs.RE05.measuredLeft_eq_trace n plan A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      NLA.Computation.LinearFamilyQuery.inner A (selectedProjection plan * B) := by
  exact @NLA.Proofs.RE05.measuredLeft_inner_selected n plan A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (A B : Square n) :
    (∑ h : Fin plan.selected.length,
      dot (A.transpose *ᵥ uColumn plan h) (B.transpose *ᵥ uColumn plan h)) =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * A)
        (selectedProjection plan * B) := by
  exact @NLA.Proofs.RE05.measuredLeft_inner_projection n plan hF A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B : Square n) (g : Fin n → ℝ) :
    dot (A *ᵥ g) (B *ᵥ g) = dot g ((A.transpose * B) *ᵥ g) := by
  exact @NLA.Proofs.RE05.dot_mulVec_quadratic n A B g
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (M : Square n) (g : Fin n → ℝ) :
    dot g (M *ᵥ g) = ∑ i : Fin n, ∑ j : Fin n, M i j * g i * g j := by
  exact @NLA.Proofs.RE05.dot_quadratic_eq_sum n M g
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω ω' : ℕ → ℝ) (copy copy' : Fin 15) :
    residualProjection (makePlan P ξ ω copy) = residualProjection (makePlan P ξ ω' copy') := by
  exact @NLA.Proofs.RE05.makePlan_residualProjection_eq n q P ξ ω ω' copy copy'
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω ω' : ℕ → ℝ) (copy copy' : Fin 15) (R : Square n) (j : Fin (q + 1)) :
    offsetQuadraticMatrix P (makePlan P ξ ω copy) R j =
      offsetQuadraticMatrix P (makePlan P ξ ω' copy') R j := by
  exact @NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq n q P ξ ω ω' copy copy' R j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (R : Square n) (j : Fin (q + 1)) :
    (offsetQuadraticMatrix P plan R j).trace =
      NLA.Computation.LinearFamilyQuery.inner (residualBasisBlock P plan j)
        (residualProjection plan * R) := by
  exact @NLA.Proofs.RE05.offsetQuadraticMatrix_trace n q P plan R j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j =
      (1 / ((makePlan P ξ ω copy).s : ℝ)) *
        (∑ g : Fin (makePlan P ξ ω copy).s,
          dot (fun k => (makePlan P ξ ω copy).G k g)
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *ᵥ
              (fun k => (makePlan P ξ ω copy).G k g))) -
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).trace := by
  exact @NLA.Proofs.RE05.actualResidualOffset_centered_unscaled n q P ξ ω copy R j hOrth
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example (q : ℕ) (ξ : ℝ) (hξ : 0 < ξ) :
    0 < gaussianWidth q ξ := by
  exact @NLA.Proofs.RE05.gaussianWidth_positive q ξ hξ
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (hξ : 0 < ξ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n)
    (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j =
      (1 / ((makePlan P ξ ω copy).s : ℝ)) *
        ∑ g : Fin (makePlan P ξ ω copy).s,
          (dot (fun k => (makePlan P ξ ω copy).G k g)
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *ᵥ
              (fun k => (makePlan P ξ ω copy).G k g)) -
            (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).trace) := by
  exact @NLA.Proofs.RE05.actualResidualOffset_centered n q P ξ hξ ω copy R j hOrth
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) (j : Fin (q + 1)) :
    offsetQuadraticMatrix P (makePlan P ξ ω copy) R j =
      (residualBasisBlock P (makePlan P ξ ω copy) j).transpose * R := by
  exact @NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection n q P ξ ω copy R j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (F : Basis n q) (R : Square n) :
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      ((F j).transpose * R) ((F j).transpose * R)) =
      (R.transpose * (∑ j : Fin (q + 1), F j * (F j).transpose) * R).trace := by
  exact @NLA.Proofs.RE05.family_transpose_product_energy n q F R
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (S R : Square n) (t : ℝ)
    (hS : (t • (1 : Square n) - S).PosSemidef) :
    (R.transpose * S * R).trace ≤ t * NLA.Computation.LinearFamilyQuery.inner R R := by
  exact @NLA.Proofs.RE05.scalar_psd_trace_bound n S R t hS
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)) ≤
      threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R := by
  exact @NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction n q P ξ ω copy R
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), 2 *
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j *
        (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j).transpose).trace) ≤
      2 * threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R := by
  exact @NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge n q P ξ ω copy R
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05CenteredOffsetGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix

/-- Literal batch rhs; original plans remain fixed, including their actual G. -/
theorem actual_rhs_centered_quadratics {n q : ℕ} (P : Basis n q)
    (ε : ℝ) (hε : 0 < ε) (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n)
    (j : Fin (q + 1))
    (hOrth : NLA.Computation.LinearFamilyQuery.inner (orthonormalMember P j) R = 0) :
    rhs (orthonormalMember P) (plans P ε ω copy)
      (copyResponses (plans P ε ω) (batchAnswers R (plans P ε ω)) copy) j =
      (1 / ((plans P ε ω copy).s : ℝ)) *
        ∑ g : Fin (plans P ε ω copy).s,
          ((∑ a : Fin n, ∑ b : Fin n,
            offsetQuadraticMatrix P (plans P ε ω copy) R j a b *
              (plans P ε ω copy).G a g * (plans P ε ω copy).G b g) -
            (offsetQuadraticMatrix P (plans P ε ω copy) R j).trace) := by
  rw [copyResponses_batchAnswers]
  have hξ : 0 < squaredAccuracy ε := by unfold squaredAccuracy; positivity
  change regressionOffset (orthonormalMember P)
    (makePlan P (squaredAccuracy ε) ω copy) R j = _
  rw [actualResidualOffset_centered P (squaredAccuracy ε) hξ ω copy R j hOrth]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  rw [dot_quadratic_eq_sum]
  rfl

theorem actual_raw_variance_charge {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    (∑ j : Fin (q + 1), 2 *
      (((residualProjection (makePlan P ξ ω copy) * orthonormalMember P j).transpose *
        (residualProjection (makePlan P ξ ω copy) * R)) *
        ((residualProjection (makePlan P ξ ω copy) * orthonormalMember P j).transpose *
          (residualProjection (makePlan P ξ ω copy) * R)).transpose).trace) ≤
      2 * threshold q ξ * (∑ a : Fin n, ∑ b : Fin n, R a b * R a b) :=
  actual_offsetQuadratic_varianceCharge P ξ ω copy R

theorem actual_width_positive {n q : ℕ} (P : Basis n q) (ε : ℝ) (hε : 0 < ε)
    (ω : ℕ → ℝ) (copy : Fin 15) : 0 < (plans P ε ω copy).s :=
  gaussianWidth_positive q (squaredAccuracy ε) (by unfold squaredAccuracy; positivity)

theorem dependent_zero_family_contraction (n q : ℕ) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (R : Square n) :
    let P : Basis n q := fun _ => 0
    (∑ j : Fin (q + 1), NLA.Computation.LinearFamilyQuery.inner
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)
      (offsetQuadraticMatrix P (makePlan P ξ ω copy) R j)) ≤
        threshold q ξ * NLA.Computation.LinearFamilyQuery.inner R R :=
  actual_offsetQuadratic_energy_contraction _ ξ ω copy R

theorem empty_rhs_zero (q : ℕ) (P : Basis 0 q) (ξ : ℝ) (ω : ℕ → ℝ)
    (copy : Fin 15) (R : Square 0) (j : Fin (q + 1)) :
    regressionOffset (orthonormalMember P) (makePlan P ξ ω copy) R j = 0 := by
  simp [regressionOffset, rhs, dot]

end RE05CenteredOffsetGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.measuredLeft_eq_trace
#print axioms NLA.Proofs.RE05.measuredLeft_eq_trace
#assert_trust kernel NLA.Proofs.RE05.measuredLeft_inner_selected
#print axioms NLA.Proofs.RE05.measuredLeft_inner_selected
#assert_trust kernel NLA.Proofs.RE05.measuredLeft_inner_projection
#print axioms NLA.Proofs.RE05.measuredLeft_inner_projection
#assert_trust kernel NLA.Proofs.RE05.dot_mulVec_quadratic
#print axioms NLA.Proofs.RE05.dot_mulVec_quadratic
#assert_trust kernel NLA.Proofs.RE05.dot_quadratic_eq_sum
#print axioms NLA.Proofs.RE05.dot_quadratic_eq_sum
#assert_trust kernel NLA.Proofs.RE05.offsetQuadraticMatrix
#print axioms NLA.Proofs.RE05.offsetQuadraticMatrix
#assert_trust kernel NLA.Proofs.RE05.offsetQuadraticMatrix_trace
#print axioms NLA.Proofs.RE05.offsetQuadraticMatrix_trace
#assert_trust kernel NLA.Proofs.RE05.actualResidualOffset_centered_unscaled
#print axioms NLA.Proofs.RE05.actualResidualOffset_centered_unscaled
#assert_trust kernel NLA.Proofs.RE05.gaussianWidth_positive
#print axioms NLA.Proofs.RE05.gaussianWidth_positive
#assert_trust kernel NLA.Proofs.RE05.actualResidualOffset_centered
#print axioms NLA.Proofs.RE05.actualResidualOffset_centered
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_drop_projection
#assert_trust kernel NLA.Proofs.RE05.family_transpose_product_energy
#print axioms NLA.Proofs.RE05.family_transpose_product_energy
#assert_trust kernel NLA.Proofs.RE05.scalar_psd_trace_bound
#print axioms NLA.Proofs.RE05.scalar_psd_trace_bound
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_energy_contraction
#assert_trust kernel NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge
#print axioms NLA.Proofs.RE05.actual_offsetQuadratic_varianceCharge
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_rhs_centered_quadratics
#print axioms RE05CenteredOffsetGeometryConsumer.actual_rhs_centered_quadratics
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_raw_variance_charge
#print axioms RE05CenteredOffsetGeometryConsumer.actual_raw_variance_charge
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.actual_width_positive
#print axioms RE05CenteredOffsetGeometryConsumer.actual_width_positive
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.dependent_zero_family_contraction
#print axioms RE05CenteredOffsetGeometryConsumer.dependent_zero_family_contraction
#assert_trust kernel RE05CenteredOffsetGeometryConsumer.empty_rhs_zero
#print axioms RE05CenteredOffsetGeometryConsumer.empty_rhs_zero
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_eq
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_eq
#assert_trust kernel NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq
#print axioms NLA.Proofs.RE05.makePlan_offsetQuadraticMatrix_eq

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#audit_named "RE05CenteredOffsetGeometryConsumer.actual_rhs_centered_quadratics" "Independent_centered_offset_Consumer" "public" "theorem"

#audit_named "RE05CenteredOffsetGeometryConsumer.actual_raw_variance_charge" "Independent_centered_offset_Consumer" "public" "theorem"

#audit_named "RE05CenteredOffsetGeometryConsumer.actual_width_positive" "Independent_centered_offset_Consumer" "public" "theorem"

#audit_named "RE05CenteredOffsetGeometryConsumer.dependent_zero_family_contraction" "Independent_centered_offset_Consumer" "public" "theorem"

#audit_named "RE05CenteredOffsetGeometryConsumer.empty_rhs_zero" "Independent_centered_offset_Consumer" "public" "theorem"

end
