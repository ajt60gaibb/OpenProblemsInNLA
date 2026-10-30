import NLA.Proofs.RE05.Attained
import NLA.Proofs.RE05.SVDTotal
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
open NLA.Computation.NonadaptiveMatrixQuery
example {n : ℕ} (A B : Square n) :
    frobenius A B = ‖matrixVector A - matrixVector B‖ := by
  exact @NLA.Proofs.RE05.frobenius_eq_norm n A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ, ∀ d : Fin (q + 1) → ℝ,
      frobenius A (represent P c) ≤ frobenius A (represent P d) := by
  exact @NLA.Proofs.RE05.exists_frobenius_minimum n q P A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example {n q : ℕ} (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) := by
  exact @NLA.Proofs.RE05.attained_optimum n q P A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery
example : NLA.Statements.RE05.AttainedOptimum := by
  exact @NLA.Proofs.RE05.attainedOptimum 
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open NLA.Computation.NonadaptiveMatrixQuery
example : SVDTotal := by
  exact @NLA.Proofs.RE05.svd_total 
end NLA.Proofs.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
open NLA.Computation.LinearFamilyQuery
open NLA.Computation.NonadaptiveMatrixQuery

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example : NLA.Statements.RE05.AttainedOptimum := NLA.Proofs.RE05.attainedOptimum
example : NLA.Computation.NonadaptiveMatrixQuery.SVDTotal := NLA.Proofs.RE05.svd_total
example (n q : ℕ) (P : Basis n q) (A : Square n) :
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) :=
  NLA.Proofs.RE05.attained_optimum P A
example : ∀ (n q : ℕ) (P : Basis n q) (A : Square n), Independent P →
    ∃ c : Fin (q + 1) → ℝ,
      frobenius A (represent P c) = NLA.Computation.LinearFamilyQuery.optimum P A ∧
      ∀ d : Fin (q + 1) → ℝ,
        NLA.Computation.LinearFamilyQuery.optimum P A ≤ frobenius A (represent P d) :=
  NLA.Proofs.RE05.attainedOptimum
example : ∀ (a b : ℕ) (B : Matrix (Fin a) (Fin b) ℝ),
    ValidSVDResult B (exactSVD B) := NLA.Proofs.RE05.svd_total

#assert_trust kernel NLA.Proofs.RE05.matrixVector
#assert_trust kernel NLA.Proofs.RE05.representationMap
#assert_trust kernel NLA.Proofs.RE05.frobenius_eq_norm
#assert_trust kernel NLA.Proofs.RE05.exists_frobenius_minimum
#assert_trust kernel NLA.Proofs.RE05.attained_optimum
#assert_trust kernel NLA.Proofs.RE05.attainedOptimum
#assert_trust kernel NLA.Proofs.RE05.svd_total
#print axioms NLA.Proofs.RE05.matrixVector
#print axioms NLA.Proofs.RE05.representationMap
#print axioms NLA.Proofs.RE05.frobenius_eq_norm
#print axioms NLA.Proofs.RE05.exists_frobenius_minimum
#print axioms NLA.Proofs.RE05.attained_optimum
#print axioms NLA.Proofs.RE05.attainedOptimum
#print axioms NLA.Proofs.RE05.svd_total

end
