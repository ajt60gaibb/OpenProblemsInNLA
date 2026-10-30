import NLA.Proofs.RE05.OneCopyError
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

#audit_named "NLA.Proofs.RE05.coefficientVector" "NLA.Proofs.RE05.CoefficientError" "public" "definition"

#audit_named "NLA.Proofs.RE05.coefficientVector_inner" "NLA.Proofs.RE05.CoefficientError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficientVector_norm_sq" "NLA.Proofs.RE05.CoefficientError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.coefficient_error_bound" "NLA.Proofs.RE05.CoefficientError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleOutput_coefficient_error" "NLA.Proofs.RE05.CoefficientError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.matrixVector_sub" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frobenius_eq_zero_iff" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.frobenius_triangle" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_orthogonal_optimum" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_pythagorean_optimum" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.optimum_eq_zero_iff" "NLA.Proofs.RE05.OrthogonalOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.represent_sub" "NLA.Proofs.RE05.OneCopyOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.orthonormal_frobenius_sq" "NLA.Proofs.RE05.OneCopyOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_orthonormal_analysis_optimum" "NLA.Proofs.RE05.OneCopyOptimum" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleCopy_squared_error_bound" "NLA.Proofs.RE05.OneCopyError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.exists_oneCopy_error_analysis" "NLA.Proofs.RE05.OneCopyError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleCopy_relative_squared" "NLA.Proofs.RE05.OneCopyError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleCopy_batch_relative_squared" "NLA.Proofs.RE05.OneCopyError" "public" "theorem"

#audit_named "NLA.Proofs.RE05.singleCopy_zero_optimum_exact" "NLA.Proofs.RE05.OneCopyError" "public" "theorem"

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
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (B : Square n) (j : Fin (q + 1)) :
    regressionOffset P plan B j =
      ⟪measurementVector plan (P j), measurementVector plan B⟫_ℝ := by
  exact @NLA.Proofs.RE05.regressionOffset_inner n q P plan B j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A B : Square n) : regressionOffset P plan (A - B) =
      regressionOffset P plan A - regressionOffset P plan B := by
  exact @NLA.Proofs.RE05.regressionOffset_sub n q P plan A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (c : Fin (q + 1) → ℝ) :
    regressionOffset P plan (represent P c) = gram P plan *ᵥ c := by
  exact @NLA.Proofs.RE05.regressionOffset_represent n q P plan c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A : Square n) (c : Fin (q + 1) → ℝ) :
    gram P plan *ᵥ (singleOutput P plan (planAnswers A plan) - c) =
      regressionOffset P plan (A - represent P c) := by
  exact @NLA.Proofs.RE05.singleOutput_residual_equation n q P plan A c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (schedule : Fin 15 → Plan n) (copy : Fin 15) (A : Square n)
    (c : Fin (q + 1) → ℝ) :
    gram P (schedule copy) *ᵥ
      (singleOutput P (schedule copy)
        (copyResponses schedule (batchAnswers A schedule) copy) - c) =
      regressionOffset P (schedule copy) (A - represent P c) := by
  exact @NLA.Proofs.RE05.singleOutput_batch_residual_equation n q P schedule copy A c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {m : ℕ} (c d : Fin m → ℝ) :
    dot c d = ⟪coefficientVector c, coefficientVector d⟫_ℝ := by
  exact @NLA.Proofs.RE05.coefficientVector_inner m c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {m : ℕ} (c : Fin m → ℝ) :
    dot c c = ‖coefficientVector c‖ ^ 2 := by
  exact @NLA.Proofs.RE05.coefficientVector_norm_sq m c
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ)
    (α : ℝ) (hα : 0 < α) (hLower : ∀ d : Fin m → ℝ, α * dot d d ≤ dot d (G *ᵥ d))
    (d z : Fin m → ℝ) (heq : G *ᵥ d = z) :
    dot d d ≤ (1 / α ^ 2) * dot z z := by
  exact @NLA.Proofs.RE05.coefficient_error_bound m G α hα hLower d z heq
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n)
    (A : Square n) (c : Fin (q + 1) → ℝ) (α : ℝ) (hα : 0 < α)
    (hLower : ∀ d : Fin (q + 1) → ℝ, α * dot d d ≤ dot d (gram P plan *ᵥ d)) :
    dot (singleOutput P plan (planAnswers A plan) - c)
      (singleOutput P plan (planAnswers A plan) - c) ≤
      (1 / α ^ 2) * dot (regressionOffset P plan (A - represent P c))
        (regressionOffset P plan (A - represent P c)) := by
  exact @NLA.Proofs.RE05.singleOutput_coefficient_error n q P plan A c α hα hLower
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (c d : Fin (q + 1) → ℝ) :
    represent P (c - d) = represent P c - represent P d := by
  exact @NLA.Proofs.RE05.represent_sub n q P c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (c d : Fin (q + 1) → ℝ) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius
      (represent (orthonormalMember P) c) (represent (orthonormalMember P) d) ^ 2 =
      dot (d - c) (d - c) := by
  exact @NLA.Proofs.RE05.orthonormal_frobenius_sq n q P hP c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) c) = optimum P A ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) = 0) ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent (orthonormalMember P) d) ^ 2 =
            optimum P A ^ 2 + dot (d - c) (d - c) := by
  exact @NLA.Proofs.RE05.exists_orthonormal_analysis_optimum n q P hP A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
        optimum P A ^ 2 + (1 / α ^ 2) *
          dot (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
            (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) := by
  exact @NLA.Proofs.RE05.singleCopy_squared_error_bound n q P hP A plan c hPyth α hα hLower
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) c) = optimum P A ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) = 0) ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c)) ∧
      ∀ (plan : Plan n) (α : ℝ), 0 < α → OrthonormalMeasurementLowerBound P plan α →
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
          optimum P A ^ 2 + (1 / α ^ 2) *
            dot (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
              (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) := by
  exact @NLA.Proofs.RE05.exists_oneCopy_error_analysis n q P hP A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (ξ : ℝ) (hLower : OrthonormalMeasurementLowerBound P plan (1 / 2))
    (hOffset : dot
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) ≤
        (ξ / 4) * optimum P A ^ 2) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P plan (planAnswers A plan))) ^ 2 ≤
        (1 + ξ) * optimum P A ^ 2 := by
  exact @NLA.Proofs.RE05.singleCopy_relative_squared n q P hP A plan c hPyth ξ hLower hOffset
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (schedule : Fin 15 → Plan n) (copy : Fin 15) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (ξ : ℝ) (hLower : OrthonormalMeasurementLowerBound P (schedule copy) (1 / 2))
    (hOffset : dot
      (regressionOffset (orthonormalMember P) (schedule copy) (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) (schedule copy) (A - represent (orthonormalMember P) c)) ≤
        (ξ / 4) * optimum P A ^ 2) :
    NLA.Computation.NonadaptiveMatrixQuery.frobenius A
      (represent P (singleOutput P (schedule copy)
        (copyResponses schedule (batchAnswers A schedule) copy))) ^ 2 ≤
        (1 + ξ) * optimum P A ^ 2 := by
  exact @NLA.Proofs.RE05.singleCopy_batch_relative_squared n q P hP A schedule copy c hPyth ξ hLower hOffset
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (hLower : OrthonormalMeasurementLowerBound P plan (1 / 2))
    (hOpt : optimum P A = 0)
    (hOffset : dot
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c))
      (regressionOffset (orthonormalMember P) plan (A - represent (orthonormalMember P) c)) ≤ 0) :
    A = represent P (singleOutput P plan (planAnswers A plan)) := by
  exact @NLA.Proofs.RE05.singleCopy_zero_optimum_exact n q P hP A plan c hPyth hLower hOpt hOffset
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05OneCopyGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix InnerProductSpace

theorem same_original_plan_residual_equation {n q : ℕ} (P : Basis n q) (A : Square n)
    (ε : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (c : Fin (q + 1) → ℝ) :
    gram (orthonormalMember P) (plans P ε ω copy) *ᵥ
      (singleOutput (orthonormalMember P) (plans P ε ω copy)
        (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy) - c) =
      rhs (orthonormalMember P) (plans P ε ω copy)
        (planAnswers (A - represent (orthonormalMember P) c) (plans P ε ω copy)) :=
  singleOutput_batch_residual_equation (orthonormalMember P) (plans P ε ω) copy A c

theorem raw_cauchy_error {m : ℕ} (G : Matrix (Fin m) (Fin m) ℝ)
    (α : ℝ) (hα : 0 < α) (hLower : ∀ d : Fin m → ℝ,
      α * (∑ i, d i * d i) ≤ ∑ i, d i * (G *ᵥ d) i)
    (d z : Fin m → ℝ) (heq : G *ᵥ d = z) :
    (∑ i, d i * d i) ≤ (1 / α ^ 2) * ∑ i, z i * z i :=
  coefficient_error_bound G α hα hLower d z heq

theorem optimum_before_all_original_plans {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) c) = optimum P A ∧
      (∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.inner (A - represent (orthonormalMember P) c)
          (represent (orthonormalMember P) d) = 0) ∧
      ∀ (ε : ℝ) (ω : ℕ → ℝ) (copy : Fin 15),
        (∀ d : Fin (q + 1) → ℝ, (1 / 2 : ℝ) * dot d d ≤
          dot d (gram (orthonormalMember P) (plans P ε ω copy) *ᵥ d)) →
        dot
          (rhs (orthonormalMember P) (plans P ε ω copy)
            (planAnswers (A - represent (orthonormalMember P) c) (plans P ε ω copy)))
          (rhs (orthonormalMember P) (plans P ε ω copy)
            (planAnswers (A - represent (orthonormalMember P) c) (plans P ε ω copy))) ≤
              (squaredAccuracy ε / 4) * optimum P A ^ 2 →
        NLA.Computation.NonadaptiveMatrixQuery.frobenius A
          (represent P (singleOutput P (plans P ε ω copy)
            (copyResponses (plans P ε ω) (batchAnswers A (plans P ε ω)) copy))) ^ 2 ≤
            (1 + squaredAccuracy ε) * optimum P A ^ 2 := by
  rcases exists_orthonormal_analysis_optimum P hP A with ⟨c, hc, ho, hp⟩
  refine ⟨c, hc, ho, fun ε ω copy hLower hOffset => ?_⟩
  exact singleCopy_batch_relative_squared P hP A (plans P ε ω) copy c hp
    (squaredAccuracy ε) hLower hOffset

theorem actual_zero_optimum {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (A : Square n) (plan : Plan n) (c : Fin (q + 1) → ℝ)
    (hPyth : ∀ d : Fin (q + 1) → ℝ,
      NLA.Computation.NonadaptiveMatrixQuery.frobenius A
        (represent (orthonormalMember P) d) ^ 2 = optimum P A ^ 2 + dot (d - c) (d - c))
    (hLower : ∀ d : Fin (q + 1) → ℝ, (1 / 2 : ℝ) * dot d d ≤
      dot d (gram (orthonormalMember P) plan *ᵥ d))
    (hOpt : optimum P A = 0)
    (hOffset : dot (rhs (orthonormalMember P) plan
      (planAnswers (A - represent (orthonormalMember P) c) plan))
      (rhs (orthonormalMember P) plan
        (planAnswers (A - represent (orthonormalMember P) c) plan)) ≤ 0) :
    A = represent P (singleOutput P plan (planAnswers A plan)) :=
  singleCopy_zero_optimum_exact P hP A plan c hPyth hLower hOpt hOffset

theorem empty_coefficient_bound (G : Matrix (Fin 0) (Fin 0) ℝ)
    (d z : Fin 0 → ℝ) (α : ℝ) (hα : 0 < α) :
    dot d d ≤ (1 / α ^ 2) * dot z z := by
  apply coefficient_error_bound G α hα (by intro c; simp [dot])
  ext i
  exact Fin.elim0 i

end RE05OneCopyGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.regressionOffset
#print axioms NLA.Proofs.RE05.regressionOffset
#assert_trust kernel NLA.Proofs.RE05.regressionOffset_inner
#print axioms NLA.Proofs.RE05.regressionOffset_inner
#assert_trust kernel NLA.Proofs.RE05.regressionOffset_sub
#print axioms NLA.Proofs.RE05.regressionOffset_sub
#assert_trust kernel NLA.Proofs.RE05.regressionOffset_represent
#print axioms NLA.Proofs.RE05.regressionOffset_represent
#assert_trust kernel NLA.Proofs.RE05.singleOutput_residual_equation
#print axioms NLA.Proofs.RE05.singleOutput_residual_equation
#assert_trust kernel NLA.Proofs.RE05.singleOutput_batch_residual_equation
#print axioms NLA.Proofs.RE05.singleOutput_batch_residual_equation
#assert_trust kernel NLA.Proofs.RE05.coefficientVector
#print axioms NLA.Proofs.RE05.coefficientVector
#assert_trust kernel NLA.Proofs.RE05.coefficientVector_inner
#print axioms NLA.Proofs.RE05.coefficientVector_inner
#assert_trust kernel NLA.Proofs.RE05.coefficientVector_norm_sq
#print axioms NLA.Proofs.RE05.coefficientVector_norm_sq
#assert_trust kernel NLA.Proofs.RE05.coefficient_error_bound
#print axioms NLA.Proofs.RE05.coefficient_error_bound
#assert_trust kernel NLA.Proofs.RE05.singleOutput_coefficient_error
#print axioms NLA.Proofs.RE05.singleOutput_coefficient_error
#assert_trust kernel NLA.Proofs.RE05.represent_sub
#print axioms NLA.Proofs.RE05.represent_sub
#assert_trust kernel NLA.Proofs.RE05.orthonormal_frobenius_sq
#print axioms NLA.Proofs.RE05.orthonormal_frobenius_sq
#assert_trust kernel NLA.Proofs.RE05.exists_orthonormal_analysis_optimum
#print axioms NLA.Proofs.RE05.exists_orthonormal_analysis_optimum
#assert_trust kernel NLA.Proofs.RE05.singleCopy_squared_error_bound
#print axioms NLA.Proofs.RE05.singleCopy_squared_error_bound
#assert_trust kernel NLA.Proofs.RE05.exists_oneCopy_error_analysis
#print axioms NLA.Proofs.RE05.exists_oneCopy_error_analysis
#assert_trust kernel NLA.Proofs.RE05.singleCopy_relative_squared
#print axioms NLA.Proofs.RE05.singleCopy_relative_squared
#assert_trust kernel NLA.Proofs.RE05.singleCopy_batch_relative_squared
#print axioms NLA.Proofs.RE05.singleCopy_batch_relative_squared
#assert_trust kernel NLA.Proofs.RE05.singleCopy_zero_optimum_exact
#print axioms NLA.Proofs.RE05.singleCopy_zero_optimum_exact
#assert_trust kernel RE05OneCopyGeometryConsumer.same_original_plan_residual_equation
#print axioms RE05OneCopyGeometryConsumer.same_original_plan_residual_equation
#assert_trust kernel RE05OneCopyGeometryConsumer.raw_cauchy_error
#print axioms RE05OneCopyGeometryConsumer.raw_cauchy_error
#assert_trust kernel RE05OneCopyGeometryConsumer.optimum_before_all_original_plans
#print axioms RE05OneCopyGeometryConsumer.optimum_before_all_original_plans
#assert_trust kernel RE05OneCopyGeometryConsumer.actual_zero_optimum
#print axioms RE05OneCopyGeometryConsumer.actual_zero_optimum
#assert_trust kernel RE05OneCopyGeometryConsumer.empty_coefficient_bound
#print axioms RE05OneCopyGeometryConsumer.empty_coefficient_bound

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#audit_named "RE05OneCopyGeometryConsumer.same_original_plan_residual_equation" "Independent_one_copy_Consumer" "public" "theorem"

#audit_named "RE05OneCopyGeometryConsumer.raw_cauchy_error" "Independent_one_copy_Consumer" "public" "theorem"

#audit_named "RE05OneCopyGeometryConsumer.optimum_before_all_original_plans" "Independent_one_copy_Consumer" "public" "theorem"

#audit_named "RE05OneCopyGeometryConsumer.actual_zero_optimum" "Independent_one_copy_Consumer" "public" "theorem"

#audit_named "RE05OneCopyGeometryConsumer.empty_coefficient_bound" "Independent_one_copy_Consumer" "public" "theorem"

end
