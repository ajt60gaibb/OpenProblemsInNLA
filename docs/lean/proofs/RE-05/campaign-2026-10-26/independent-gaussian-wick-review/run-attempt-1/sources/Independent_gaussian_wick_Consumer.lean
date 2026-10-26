import NLA.Proofs.RE05.GaussianWick
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

#audit_named "NLA.Proofs.RE05.gaussian_power_integrable" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_first_integral" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_second_integral" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_product_powers_integrable" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_product_powers_integral" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_third_integral" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_mgf_deriv_one" "NLA.Proofs.RE05.GaussianMoments" "private" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_mgf_deriv_two" "NLA.Proofs.RE05.GaussianMoments" "private" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_mgf_deriv_three" "NLA.Proofs.RE05.GaussianMoments" "private" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_mgf_deriv_four" "NLA.Proofs.RE05.GaussianMoments" "private" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_fourth_integral" "NLA.Proofs.RE05.GaussianMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.quarticMultiplicity" "NLA.Proofs.RE05.GaussianWick" "public" "definition"

#audit_named "NLA.Proofs.RE05.quartic_eq_product_powers" "NLA.Proofs.RE05.GaussianWick" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_quartic_integrable" "NLA.Proofs.RE05.GaussianWick" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_wick_four" "NLA.Proofs.RE05.GaussianWick" "public" "theorem"

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
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) (x : ι → ℝ) :
    x a * x b * x c * x d = ∏ i, x i ^ quarticMultiplicity a b c d i := by
  exact @NLA.Proofs.RE05.quartic_eq_product_powers ι (inferInstance) (inferInstance) a b c d x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    Integrable (fun x : ι → ℝ => x a * x b * x c * x d)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_quartic_integrable ι (inferInstance) (inferInstance) a b c d
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b c d : ι) :
    (∫ x : ι → ℝ, x a * x b * x c * x d
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) := by
  exact @NLA.Proofs.RE05.gaussian_wick_four ι (inferInstance) (inferInstance) a b c d
end NLA.Proofs.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) (x : ι → ℝ) :
    x a * x b * x c * x d = ∏ i, x i ^ quarticMultiplicity a b c d i :=
  quartic_eq_product_powers a b c d x
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    Integrable (fun x : ι → ℝ => x a * x b * x c * x d)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := gaussian_quartic_integrable a b c d
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b c d : ι) :
    (∫ x : ι → ℝ, x a * x b * x c * x d
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (if a = b ∧ c = d then 1 else 0) +
        (if a = c ∧ b = d then 1 else 0) + (if a = d ∧ b = c then 1 else 0) :=
  gaussian_wick_four a b c d
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι) :
    (∫ x : ι → ℝ, x a * x a * x a * x a
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 3 := by
  have h := gaussian_wick_four a a a a
  norm_num at h
  exact h
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) (hab : a ≠ b) :
    (∫ x : ι → ℝ, x a * x b * x a * x b
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 1 := by
  simpa [hab, Ne.symm hab] using gaussian_wick_four a b a b

#assert_trust kernel quarticMultiplicity
#assert_trust kernel quartic_eq_product_powers
#assert_trust kernel gaussian_quartic_integrable
#assert_trust kernel gaussian_wick_four
#print axioms quarticMultiplicity
#print axioms quartic_eq_product_powers
#print axioms gaussian_quartic_integrable
#print axioms gaussian_wick_four

end
