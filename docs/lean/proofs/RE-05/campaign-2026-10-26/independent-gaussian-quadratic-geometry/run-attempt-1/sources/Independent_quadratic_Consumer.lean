import NLA.Proofs.RE05.GaussianQuadraticCovariance
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

#audit_named "NLA.Proofs.RE05.gaussian_coordinate_memLp" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_pair_integrable" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_coordinate_mean" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_pair_integral" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussianQuadraticForm" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "definition"

#audit_named "NLA.Proofs.RE05.gaussian_quadratic_integrable" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_quadratic_mean" "NLA.Proofs.RE05.GaussianQuadraticMoments" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_quadratic_product_expand" "NLA.Proofs.RE05.GaussianQuadraticProduct" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_quadratic_product_integrable" "NLA.Proofs.RE05.GaussianQuadraticProduct" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_wick_contraction" "NLA.Proofs.RE05.GaussianQuadraticProduct" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_quadratic_product_integral" "NLA.Proofs.RE05.GaussianQuadraticProduct" "public" "theorem"

#audit_named "NLA.Proofs.RE05.centeredGaussianQuadraticForm" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "definition"

#audit_named "NLA.Proofs.RE05.gaussian_centered_quadratic_integrable" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_centered_quadratic_mean" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_centered_product_expand" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_centered_product_integrable" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_centered_product_integral" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.real_matrix_trace_square_le_frobenius" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

#audit_named "NLA.Proofs.RE05.gaussian_centered_quadratic_variance_le" "NLA.Proofs.RE05.GaussianQuadraticCovariance" "public" "theorem"

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
example {ι : Type*} [Fintype ι] (i : ι) (p : NNReal) :
    MemLp (fun x : ι → ℝ => x i) p (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_coordinate_memLp ι (inferInstance) i p
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] (a b : ι) :
    Integrable (fun x : ι → ℝ => x a * x b)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_pair_integrable ι (inferInstance) a b
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] (i : ι) :
    (∫ x : ι → ℝ, x i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
  exact @NLA.Proofs.RE05.gaussian_coordinate_mean ι (inferInstance) i
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι] (a b : ι) :
    (∫ x : ι → ℝ, x a * x b ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      if a = b then 1 else 0 := by
  exact @NLA.Proofs.RE05.gaussian_pair_integral ι (inferInstance) (inferInstance) a b
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] (A : Matrix ι ι ℝ) :
    Integrable (gaussianQuadraticForm A) (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_quadratic_integrable ι (inferInstance) A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, gaussianQuadraticForm A x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = A.trace := by
  exact @NLA.Proofs.RE05.gaussian_quadratic_mean ι (inferInstance) (inferInstance) A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    gaussianQuadraticForm A x * gaussianQuadraticForm B x =
      ∑ p : (ι × ι) × (ι × ι),
        (A p.1.1 p.1.2 * B p.2.1 p.2.2) *
          (x p.1.1 * x p.1.2 * x p.2.1 * x p.2.2) := by
  exact @NLA.Proofs.RE05.gaussian_quadratic_product_expand ι (inferInstance) A B x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Integrable (fun x : ι → ℝ => gaussianQuadraticForm A x * gaussianQuadraticForm B x)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_quadratic_product_integrable ι (inferInstance) (inferInstance) A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∑ p : (ι × ι) × (ι × ι),
      (A p.1.1 p.1.2 * B p.2.1 p.2.2) *
        ((if p.1.1 = p.1.2 ∧ p.2.1 = p.2.2 then 1 else 0) +
          (if p.1.1 = p.2.1 ∧ p.1.2 = p.2.2 then 1 else 0) +
          (if p.1.1 = p.2.2 ∧ p.1.2 = p.2.1 then 1 else 0))) =
      A.trace * B.trace + (A * B).trace + (A * B.transpose).trace := by
  exact @NLA.Proofs.RE05.gaussian_wick_contraction ι (inferInstance) (inferInstance) A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, gaussianQuadraticForm A x * gaussianQuadraticForm B x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      A.trace * B.trace + (A * B).trace + (A * B.transpose).trace := by
  exact @NLA.Proofs.RE05.gaussian_quadratic_product_integral ι (inferInstance) (inferInstance) A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) :
    Integrable (centeredGaussianQuadraticForm A)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_centered_quadratic_integrable ι (inferInstance) A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, centeredGaussianQuadraticForm A x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) = 0 := by
  exact @NLA.Proofs.RE05.gaussian_centered_quadratic_mean ι (inferInstance) (inferInstance) A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) (x : ι → ℝ) :
    centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x =
      gaussianQuadraticForm A x * gaussianQuadraticForm B x -
        B.trace * gaussianQuadraticForm A x - A.trace * gaussianQuadraticForm B x +
        A.trace * B.trace := by
  exact @NLA.Proofs.RE05.gaussian_centered_product_expand ι (inferInstance) A B x
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    Integrable (fun x : ι → ℝ =>
      centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_centered_product_integrable ι (inferInstance) (inferInstance) A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, centeredGaussianQuadraticForm A x * centeredGaussianQuadraticForm B x
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      (A * B).trace + (A * B.transpose).trace := by
  exact @NLA.Proofs.RE05.gaussian_centered_product_integral ι (inferInstance) (inferInstance) A B
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) : (A * A).trace ≤ (A * A.transpose).trace := by
  exact @NLA.Proofs.RE05.real_matrix_trace_square_le_frobenius ι (inferInstance) A
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) :
    (∫ x : ι → ℝ, (centeredGaussianQuadraticForm A x) ^ 2
      ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) ≤
      2 * (A * A.transpose).trace := by
  exact @NLA.Proofs.RE05.gaussian_centered_quadratic_variance_le ι (inferInstance) (inferInstance) A
end NLA.Proofs.RE05

namespace IndependentGaussianQuadraticEdges
open NLA.Proofs.RE05 MeasureTheory ProbabilityTheory

def upper : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 0, 0]
def skew : Matrix (Fin 2) (Fin 2) ℝ := !![0, 3; -3, 0]

theorem upper_variance : (∫ x : Fin 2 → ℝ,
    centeredGaussianQuadraticForm upper x * centeredGaussianQuadraticForm upper x
    ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 4 := by
  have h := gaussian_centered_product_integral upper upper
  norm_num [upper, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two] at h
  exact h

theorem skew_variance : (∫ x : Fin 2 → ℝ,
    centeredGaussianQuadraticForm skew x * centeredGaussianQuadraticForm skew x
    ∂Measure.pi (fun _ : Fin 2 => gaussianReal 0 1)) = 0 := by
  have h := gaussian_centered_product_integral skew skew
  norm_num [skew, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two] at h
  exact h

theorem scalar_covariance : (∫ x : Fin 1 → ℝ,
    centeredGaussianQuadraticForm !![3] x * centeredGaussianQuadraticForm !![5] x
    ∂Measure.pi (fun _ : Fin 1 => gaussianReal 0 1)) = 30 := by
  have h := gaussian_centered_product_integral
    (!![3] : Matrix (Fin 1) (Fin 1) ℝ) !![5]
  norm_num [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply] at h
  exact h

theorem empty_joint (A B : Matrix (Fin 0) (Fin 0) ℝ) :
    (∫ x : Fin 0 → ℝ, gaussianQuadraticForm A x * gaussianQuadraticForm B x
      ∂Measure.pi (fun _ : Fin 0 => gaussianReal 0 1)) = 0 := by
  simpa [Matrix.trace] using gaussian_quadratic_product_integral A B

theorem literal_target_identity : NLA.Statements.RE05.Target =
    NLA.ReviewedStatements.RE05.Target := rfl

#assert_trust kernel upper
#assert_trust kernel skew
#assert_trust kernel upper_variance
#assert_trust kernel skew_variance
#assert_trust kernel scalar_covariance
#assert_trust kernel empty_joint
#assert_trust kernel literal_target_identity
#print axioms upper_variance
#print axioms skew_variance
#print axioms scalar_covariance
#print axioms empty_joint
#print axioms literal_target_identity
end IndependentGaussianQuadraticEdges

end
