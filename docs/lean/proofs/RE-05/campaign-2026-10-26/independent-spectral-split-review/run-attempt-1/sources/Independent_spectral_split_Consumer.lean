import NLA.Proofs.RE05.BasisProjection
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
example {n : ℕ} (plan : Plan n) :
    selectedProjection plan + residualProjection plan = 1 := by
  exact @NLA.Proofs.RE05.projection_add_residual n plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) :
    (selectedProjection plan).IsSymm := by
  exact @NLA.Proofs.RE05.selectedProjection_symmetric n plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) :
    (residualProjection plan).IsSymm := by
  exact @NLA.Proofs.RE05.residualProjection_symmetric n plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) (x : Fin n → ℝ) :
    complement plan x = residualProjection plan *ᵥ x := by
  exact @NLA.Proofs.RE05.complement_eq_mulVec n plan x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) (x y : Fin n → ℝ) :
    dot (complement plan x) y = dot x (complement plan y) := by
  exact @NLA.Proofs.RE05.complement_selfAdjoint n plan x y
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (makePlan P ξ ω copy).selected.Nodup := by
  exact @NLA.Proofs.RE05.makePlan_selected_nodup n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (planFrame (makePlan P ξ ω copy)).transpose * planFrame (makePlan P ξ ω copy) = 1 := by
  exact @NLA.Proofs.RE05.makePlan_frame_gram n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    selectedProjection plan * selectedProjection plan = selectedProjection plan := by
  exact @NLA.Proofs.RE05.selectedProjection_idempotent n plan hF
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    residualProjection plan * residualProjection plan = residualProjection plan := by
  exact @NLA.Proofs.RE05.residualProjection_idempotent n plan hF
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    complement (makePlan P ξ ω copy) (complement (makePlan P ξ ω copy) x) =
      complement (makePlan P ξ ω copy) x := by
  exact @NLA.Proofs.RE05.makePlan_complement_idempotent n q P ξ ω copy x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (makePlan P ξ ω copy) * selectedProjection (makePlan P ξ ω copy) =
      selectedProjection (makePlan P ξ ω copy) := by
  exact @NLA.Proofs.RE05.makePlan_selectedProjection_idempotent n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) * residualProjection (makePlan P ξ ω copy) =
      residualProjection (makePlan P ξ ω copy) := by
  exact @NLA.Proofs.RE05.makePlan_residualProjection_idempotent n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n) (E : Square n) :
    selectedProjection plan * E + residualProjection plan * E = E := by
  exact @NLA.Proofs.RE05.projection_basis_split n plan E
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    selectedProjection plan * residualProjection plan = 0 := by
  exact @NLA.Proofs.RE05.selected_residual_mul_zero n plan hF
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) :
    residualProjection plan * selectedProjection plan = 0 := by
  exact @NLA.Proofs.RE05.residual_selected_mul_zero n plan hF
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j : Fin n)
    (hs : 0 < squareSingularValues sigma j) (i : Fin n) : U i j = V i j := by
  exact @NLA.Proofs.RE05.validSVD_posSemidef_positive_column n B U V sigma h hB j hs i
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) (j i : Fin n) :
    squareSingularValues sigma j * V i j = squareSingularValues sigma j * U i j := by
  exact @NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry n B U V sigma h hB j i
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.SVDMachine
example {n : ℕ}
    {B U V : Matrix (Fin n) (Fin n) ℝ} {sigma : Fin (min n n) → ℝ}
    (h : ValidSVD B U sigma V) (hB : B.PosSemidef) :
    B = U * Matrix.diagonal (squareSingularValues sigma) * U.transpose := by
  exact @NLA.Proofs.RE05.validSVD_posSemidef_diagonalization n B U V sigma h hB
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n : ℕ} {B U V : Square n}
    {sigma : Fin (min n n) → ℝ} (h : ValidSVD B U sigma V) : U.transpose * U = 1 := by
  exact @NLA.Proofs.RE05.validSVD_left_gram n B U V sigma h
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) :
    (leverageFrame P).transpose * leverageFrame P = 1 := by
  exact @NLA.Proofs.RE05.leverageFrame_gram n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) :
    leverageFrame P * (leverageFrame P).transpose = 1 := by
  exact @NLA.Proofs.RE05.leverageFrame_cogram n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n : ℕ} (U : Square n) (hU : U.transpose * U = 1)
    (A B : Square n) :
    (U * A * U.transpose) * (U * B * U.transpose) = U * (A * B) * U.transpose := by
  exact @NLA.Proofs.RE05.frame_conjugate_mul n U hU A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (f : Fin n → ℝ) :
    (∑ h : Fin (makePlan P ξ ω copy).selected.length,
      f (makePlan P ξ ω copy).selected[h]) =
      ∑ j : Fin n, if threshold q ξ < leverageSingularValues P j then f j else 0 := by
  exact @NLA.Proofs.RE05.makePlan_sum_selected n q P ξ ω copy f
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (makePlan P ξ ω copy) =
      leverageFrame P * Matrix.diagonal (selectedMask P ξ) * (leverageFrame P).transpose := by
  exact @NLA.Proofs.RE05.makePlan_selectedProjection_mask n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) (ξ : ℝ) :
    Matrix.diagonal (residualMask P ξ) = 1 - Matrix.diagonal (selectedMask P ξ) := by
  exact @NLA.Proofs.RE05.residualMask_diagonal n q P ξ
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) =
      leverageFrame P * Matrix.diagonal (residualMask P ξ) * (leverageFrame P).transpose := by
  exact @NLA.Proofs.RE05.makePlan_residualProjection_mask n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) :
    leverage P = leverageFrame P * Matrix.diagonal (leverageSingularValues P) *
      (leverageFrame P).transpose := by
  exact @NLA.Proofs.RE05.leverage_diagonalization n q P
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.SVDMachine
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (residualProjection (makePlan P ξ ω copy)).PosSemidef := by
  exact @NLA.Proofs.RE05.makePlan_residualProjection_posSemidef n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ) :
    Matrix.diagonal (residualMask P ξ) * Matrix.diagonal (leverageSingularValues P) *
      Matrix.diagonal (residualMask P ξ) = Matrix.diagonal (residualSingularValues P ξ) := by
  exact @NLA.Proofs.RE05.residualMask_spectrum n q P ξ
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (makePlan P ξ ω copy) * leverage P *
      residualProjection (makePlan P ξ ω copy) =
        leverageFrame P * Matrix.diagonal (residualSingularValues P ξ) *
          (leverageFrame P).transpose := by
  exact @NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (j : Fin n) : residualSingularValues P ξ j ≤ threshold q ξ := by
  exact @NLA.Proofs.RE05.residualSingularValues_le_threshold n q P ξ j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (t : ℝ) :
    leverageFrame P * Matrix.diagonal (fun _ : Fin n => t) * (leverageFrame P).transpose =
      t • (1 : Square n) := by
  exact @NLA.Proofs.RE05.frame_constant_diagonal n q P t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (threshold q ξ • (1 : Square n) -
      residualProjection (makePlan P ξ ω copy) * leverage P *
        residualProjection (makePlan P ξ ω copy)).PosSemidef := by
  exact @NLA.Proofs.RE05.makePlan_residualLeverage_bound n q P ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (ξ : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    dot (complement (makePlan P ξ ω copy) x)
      (leverage P *ᵥ complement (makePlan P ξ ω copy) x) ≤
        threshold q ξ * dot x x := by
  exact @NLA.Proofs.RE05.makePlan_residualLeverage_quadratic n q P ξ ω copy x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (∑ j : Fin (q + 1), residualBasisBlock P plan j * (residualBasisBlock P plan j).transpose) =
      residualProjection plan * leverage P * residualProjection plan := by
  exact @NLA.Proofs.RE05.residualBasisBlock_gram n q P plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) (j : Fin (q + 1)) :
    selectedProjection plan * orthonormalMember P j + residualBasisBlock P plan j =
      orthonormalMember P j := by
  exact @NLA.Proofs.RE05.actual_basis_split n q P plan j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A B = (A.transpose * B).trace := by
  exact @NLA.Proofs.RE05.matrix_inner_trace n A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A B = NLA.Computation.LinearFamilyQuery.inner B A := by
  exact @NLA.Proofs.RE05.matrix_inner_comm n A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B C : Square n) :
    NLA.Computation.LinearFamilyQuery.inner (A + B) C =
      NLA.Computation.LinearFamilyQuery.inner A C + NLA.Computation.LinearFamilyQuery.inner B C := by
  exact @NLA.Proofs.RE05.matrix_inner_add_left n A B C
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A B C : Square n) :
    NLA.Computation.LinearFamilyQuery.inner A (B + C) =
      NLA.Computation.LinearFamilyQuery.inner A B + NLA.Computation.LinearFamilyQuery.inner A C := by
  exact @NLA.Proofs.RE05.matrix_inner_add_right n A B C
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (A : Square n) :
    0 ≤ NLA.Computation.LinearFamilyQuery.inner A A := by
  exact @NLA.Proofs.RE05.matrix_inner_self_nonnegative n A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * E)
      (residualProjection plan * F) = 0 := by
  exact @NLA.Proofs.RE05.projection_matrix_inner_cross n plan hF E F
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n : ℕ} (plan : Plan n)
    (hF : (planFrame plan).transpose * planFrame plan = 1) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner E F =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection plan * E) (selectedProjection plan * F) +
        NLA.Computation.LinearFamilyQuery.inner (residualProjection plan * E) (residualProjection plan * F) := by
  exact @NLA.Proofs.RE05.projection_matrix_inner_split n plan hF E F
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.inner
      (residualBasisBlock P (makePlan P ξ ω copy) j)
      (residualBasisBlock P (makePlan P ξ ω copy) j) ≤ 1 := by
  exact @NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one n q P hP ξ ω copy j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.norm n (residualBasisBlock P (makePlan P ξ ω copy) j) ≤ 1 := by
  exact @NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one n q P hP ξ ω copy j
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (F : Basis n q) :
    (matrixFamilyGram F).PosSemidef := by
  exact @NLA.Proofs.RE05.matrixFamilyGram_posSemidef n q F
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (selectedBasisGram P plan).PosSemidef := by
  exact @NLA.Proofs.RE05.selectedBasisGram_posSemidef n q P plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (plan : Plan n) :
    (residualBasisGram P plan).PosSemidef := by
  exact @NLA.Proofs.RE05.residualBasisGram_posSemidef n q P plan
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedBasisGram P (makePlan P ξ ω copy) + residualBasisGram P (makePlan P ξ ω copy) = 1 := by
  exact @NLA.Proofs.RE05.makePlan_basisGram_split n q P hP ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    (1 - residualBasisGram P (makePlan P ξ ω copy)).PosSemidef := by
  exact @NLA.Proofs.RE05.makePlan_residualBasisGram_le_one n q P hP ξ ω copy
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
example {n q : ℕ} (P : Basis n q) (hP : Independent P)
    (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    (1 - selectedBasisGram P (makePlan P ξ ω copy)).PosSemidef := by
  exact @NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one n q P hP ξ ω copy
end NLA.Proofs.RE05


set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace RE05SpectralSplitGeometryConsumer
open NLA.Computation.LinearFamilyQuery
open NLA.Proofs.RE05
open scoped BigOperators Matrix

theorem actual_complement_selfAdjoint {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x y : Fin n → ℝ) :
    dot (complement (plans P ε ω copy) x) y = dot x (complement (plans P ε ω copy) y) :=
  complement_selfAdjoint _ x y

theorem actual_complement_idempotent {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    complement (plans P ε ω copy) (complement (plans P ε ω copy) x) =
      complement (plans P ε ω copy) x := makePlan_complement_idempotent P (squaredAccuracy ε) ω copy x

theorem actual_residual_matrix_idempotent {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    residualProjection (plans P ε ω copy) * residualProjection (plans P ε ω copy) =
      residualProjection (plans P ε ω copy) :=
  makePlan_residualProjection_idempotent P (squaredAccuracy ε) ω copy

theorem actual_residual_leverage_bound {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (threshold q (squaredAccuracy ε) • (1 : Square n) -
      residualProjection (plans P ε ω copy) * leverage P *
        residualProjection (plans P ε ω copy)).PosSemidef :=
  makePlan_residualLeverage_bound P (squaredAccuracy ε) ω copy

theorem actual_residual_quadratic {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (x : Fin n → ℝ) :
    dot (complement (plans P ε ω copy) x)
      (leverage P *ᵥ complement (plans P ε ω copy) x) ≤
        threshold q (squaredAccuracy ε) * dot x x :=
  makePlan_residualLeverage_quadratic P (squaredAccuracy ε) ω copy x

theorem literal_residual_block_sum {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    (∑ j : Fin (q + 1),
      (residualProjection (plans P ε ω copy) * orthonormalMember P j) *
        (residualProjection (plans P ε ω copy) * orthonormalMember P j).transpose) =
      residualProjection (plans P ε ω copy) * leverage P * residualProjection (plans P ε ω copy) :=
  residualBasisBlock_gram P _

theorem row_K_add_H {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedProjection (plans P ε ω copy) + residualProjection (plans P ε ω copy) = 1 :=
  projection_add_residual _

theorem coefficient_K_add_H {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) :
    selectedBasisGram P (plans P ε ω copy) + residualBasisGram P (plans P ε ω copy) = 1 :=
  makePlan_basisGram_split P hP (squaredAccuracy ε) ω copy

theorem coefficient_H_psd {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (residualBasisGram P (plans P ε ω copy)).PosSemidef :=
  residualBasisGram_posSemidef _ _

theorem coefficient_H_le_I {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) : (1 - residualBasisGram P (plans P ε ω copy)).PosSemidef :=
  makePlan_residualBasisGram_le_one P hP (squaredAccuracy ε) ω copy

theorem actual_residual_basis_norm {n q : ℕ} (P : Basis n q) (hP : Independent P) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (j : Fin (q + 1)) :
    NLA.Computation.LinearFamilyQuery.norm n
      (residualProjection (plans P ε ω copy) * orthonormalMember P j) ≤ 1 :=
  makePlan_residualBasis_norm_le_one P hP (squaredAccuracy ε) ω copy j

theorem actual_basis_frobenius_split {n q : ℕ} (P : Basis n q) (ε : ℝ)
    (ω : ℕ → ℝ) (copy : Fin 15) (E F : Square n) :
    NLA.Computation.LinearFamilyQuery.inner E F =
      NLA.Computation.LinearFamilyQuery.inner (selectedProjection (plans P ε ω copy) * E)
        (selectedProjection (plans P ε ω copy) * F) +
      NLA.Computation.LinearFamilyQuery.inner (residualProjection (plans P ε ω copy) * E)
        (residualProjection (plans P ε ω copy) * F) :=
  projection_matrix_inner_split _ (makePlan_frame_gram P (squaredAccuracy ε) ω copy) E F

theorem dependent_zero_family_bound (n q : ℕ) (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15) :
    let P : Basis n q := fun _ => 0
    (threshold q ξ • (1 : Square n) - residualProjection (makePlan P ξ ω copy) * leverage P *
      residualProjection (makePlan P ξ ω copy)).PosSemidef :=
  makePlan_residualLeverage_bound _ ξ ω copy

theorem empty_complement (q : ℕ) (P : Basis 0 q) (ξ : ℝ) (ω : ℕ → ℝ) (copy : Fin 15)
    (x : Fin 0 → ℝ) : complement (makePlan P ξ ω copy) x = x := by
  funext i
  exact Fin.elim0 i

theorem preserved_full_target_identity :
    NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel actual_complement_selfAdjoint
#assert_trust kernel actual_complement_idempotent
#assert_trust kernel actual_residual_matrix_idempotent
#assert_trust kernel actual_residual_leverage_bound
#assert_trust kernel actual_residual_quadratic
#assert_trust kernel literal_residual_block_sum
#assert_trust kernel row_K_add_H
#assert_trust kernel coefficient_K_add_H
#assert_trust kernel coefficient_H_psd
#assert_trust kernel coefficient_H_le_I
#assert_trust kernel actual_residual_basis_norm
#assert_trust kernel actual_basis_frobenius_split
#assert_trust kernel dependent_zero_family_bound
#assert_trust kernel empty_complement
#assert_trust kernel preserved_full_target_identity
#print axioms actual_complement_selfAdjoint
#print axioms actual_complement_idempotent
#print axioms actual_residual_leverage_bound
#print axioms actual_residual_quadratic
#print axioms literal_residual_block_sum
#print axioms coefficient_K_add_H
#print axioms coefficient_H_le_I
#print axioms actual_residual_basis_norm
#print axioms actual_basis_frobenius_split
#print axioms dependent_zero_family_bound
#print axioms empty_complement
#print axioms preserved_full_target_identity
end RE05SpectralSplitGeometryConsumer

#assert_trust kernel NLA.Proofs.RE05.planFrame
#print axioms NLA.Proofs.RE05.planFrame
#assert_trust kernel NLA.Proofs.RE05.selectedProjection
#print axioms NLA.Proofs.RE05.selectedProjection
#assert_trust kernel NLA.Proofs.RE05.residualProjection
#print axioms NLA.Proofs.RE05.residualProjection
#assert_trust kernel NLA.Proofs.RE05.projection_add_residual
#print axioms NLA.Proofs.RE05.projection_add_residual
#assert_trust kernel NLA.Proofs.RE05.selectedProjection_symmetric
#print axioms NLA.Proofs.RE05.selectedProjection_symmetric
#assert_trust kernel NLA.Proofs.RE05.residualProjection_symmetric
#print axioms NLA.Proofs.RE05.residualProjection_symmetric
#assert_trust kernel NLA.Proofs.RE05.complement_eq_mulVec
#print axioms NLA.Proofs.RE05.complement_eq_mulVec
#assert_trust kernel NLA.Proofs.RE05.complement_selfAdjoint
#print axioms NLA.Proofs.RE05.complement_selfAdjoint
#assert_trust kernel NLA.Proofs.RE05.makePlan_selected_nodup
#print axioms NLA.Proofs.RE05.makePlan_selected_nodup
#assert_trust kernel NLA.Proofs.RE05.makePlan_frame_gram
#print axioms NLA.Proofs.RE05.makePlan_frame_gram
#assert_trust kernel NLA.Proofs.RE05.selectedProjection_idempotent
#print axioms NLA.Proofs.RE05.selectedProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.residualProjection_idempotent
#print axioms NLA.Proofs.RE05.residualProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_complement_idempotent
#print axioms NLA.Proofs.RE05.makePlan_complement_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedProjection_idempotent
#print axioms NLA.Proofs.RE05.makePlan_selectedProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_idempotent
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_idempotent
#assert_trust kernel NLA.Proofs.RE05.projection_basis_split
#print axioms NLA.Proofs.RE05.projection_basis_split
#assert_trust kernel NLA.Proofs.RE05.selected_residual_mul_zero
#print axioms NLA.Proofs.RE05.selected_residual_mul_zero
#assert_trust kernel NLA.Proofs.RE05.residual_selected_mul_zero
#print axioms NLA.Proofs.RE05.residual_selected_mul_zero
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_positive_column
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_positive_column
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_weighted_entry
#assert_trust kernel NLA.Proofs.RE05.validSVD_posSemidef_diagonalization
#print axioms NLA.Proofs.RE05.validSVD_posSemidef_diagonalization
#assert_trust kernel NLA.Proofs.RE05.leverageFrame
#print axioms NLA.Proofs.RE05.leverageFrame
#assert_trust kernel NLA.Proofs.RE05.leverageSingularValues
#print axioms NLA.Proofs.RE05.leverageSingularValues
#assert_trust kernel NLA.Proofs.RE05.selectedMask
#print axioms NLA.Proofs.RE05.selectedMask
#assert_trust kernel NLA.Proofs.RE05.residualMask
#print axioms NLA.Proofs.RE05.residualMask
#assert_trust kernel NLA.Proofs.RE05.validSVD_left_gram
#print axioms NLA.Proofs.RE05.validSVD_left_gram
#assert_trust kernel NLA.Proofs.RE05.leverageFrame_gram
#print axioms NLA.Proofs.RE05.leverageFrame_gram
#assert_trust kernel NLA.Proofs.RE05.leverageFrame_cogram
#print axioms NLA.Proofs.RE05.leverageFrame_cogram
#assert_trust kernel NLA.Proofs.RE05.frame_conjugate_mul
#print axioms NLA.Proofs.RE05.frame_conjugate_mul
#assert_trust kernel NLA.Proofs.RE05.makePlan_sum_selected
#print axioms NLA.Proofs.RE05.makePlan_sum_selected
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedProjection_mask
#print axioms NLA.Proofs.RE05.makePlan_selectedProjection_mask
#assert_trust kernel NLA.Proofs.RE05.residualMask_diagonal
#print axioms NLA.Proofs.RE05.residualMask_diagonal
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_mask
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_mask
#assert_trust kernel NLA.Proofs.RE05.leverage_diagonalization
#print axioms NLA.Proofs.RE05.leverage_diagonalization
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualProjection_posSemidef
#print axioms NLA.Proofs.RE05.makePlan_residualProjection_posSemidef
#assert_trust kernel NLA.Proofs.RE05.residualSingularValues
#print axioms NLA.Proofs.RE05.residualSingularValues
#assert_trust kernel NLA.Proofs.RE05.residualMask_spectrum
#print axioms NLA.Proofs.RE05.residualMask_spectrum
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_diagonalization
#assert_trust kernel NLA.Proofs.RE05.residualSingularValues_le_threshold
#print axioms NLA.Proofs.RE05.residualSingularValues_le_threshold
#assert_trust kernel NLA.Proofs.RE05.frame_constant_diagonal
#print axioms NLA.Proofs.RE05.frame_constant_diagonal
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_bound
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_bound
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualLeverage_quadratic
#print axioms NLA.Proofs.RE05.makePlan_residualLeverage_quadratic
#assert_trust kernel NLA.Proofs.RE05.residualBasisBlock
#print axioms NLA.Proofs.RE05.residualBasisBlock
#assert_trust kernel NLA.Proofs.RE05.residualBasisBlock_gram
#print axioms NLA.Proofs.RE05.residualBasisBlock_gram
#assert_trust kernel NLA.Proofs.RE05.actual_basis_split
#print axioms NLA.Proofs.RE05.actual_basis_split
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_trace
#print axioms NLA.Proofs.RE05.matrix_inner_trace
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_comm
#print axioms NLA.Proofs.RE05.matrix_inner_comm
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_add_left
#print axioms NLA.Proofs.RE05.matrix_inner_add_left
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_add_right
#print axioms NLA.Proofs.RE05.matrix_inner_add_right
#assert_trust kernel NLA.Proofs.RE05.matrix_inner_self_nonnegative
#print axioms NLA.Proofs.RE05.matrix_inner_self_nonnegative
#assert_trust kernel NLA.Proofs.RE05.projection_matrix_inner_cross
#print axioms NLA.Proofs.RE05.projection_matrix_inner_cross
#assert_trust kernel NLA.Proofs.RE05.projection_matrix_inner_split
#print axioms NLA.Proofs.RE05.projection_matrix_inner_split
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasis_inner_le_one
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasis_norm_le_one
#assert_trust kernel NLA.Proofs.RE05.matrixFamilyGram
#print axioms NLA.Proofs.RE05.matrixFamilyGram
#assert_trust kernel NLA.Proofs.RE05.matrixFamilyGram_posSemidef
#print axioms NLA.Proofs.RE05.matrixFamilyGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.selectedBasisGram
#print axioms NLA.Proofs.RE05.selectedBasisGram
#assert_trust kernel NLA.Proofs.RE05.residualBasisGram
#print axioms NLA.Proofs.RE05.residualBasisGram
#assert_trust kernel NLA.Proofs.RE05.selectedBasisGram_posSemidef
#print axioms NLA.Proofs.RE05.selectedBasisGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.residualBasisGram_posSemidef
#print axioms NLA.Proofs.RE05.residualBasisGram_posSemidef
#assert_trust kernel NLA.Proofs.RE05.makePlan_basisGram_split
#print axioms NLA.Proofs.RE05.makePlan_basisGram_split
#assert_trust kernel NLA.Proofs.RE05.makePlan_residualBasisGram_le_one
#print axioms NLA.Proofs.RE05.makePlan_residualBasisGram_le_one
#assert_trust kernel NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one
#print axioms NLA.Proofs.RE05.makePlan_selectedBasisGram_le_one

end
