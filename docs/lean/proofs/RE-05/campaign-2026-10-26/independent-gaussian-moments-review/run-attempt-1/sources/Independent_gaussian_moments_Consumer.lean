import NLA.Proofs.RE05.GaussianMoments
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
example (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  exact @NLA.Proofs.RE05.gaussian_power_integrable k
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example : ∫ x : ℝ, x ∂gaussianReal 0 1 = 0 := by
  exact @NLA.Proofs.RE05.gaussian_first_integral 
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
  exact @NLA.Proofs.RE05.gaussian_second_integral 
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ k i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
  exact @NLA.Proofs.RE05.gaussian_product_powers_integrable ι (inferInstance) k
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 := by
  exact @NLA.Proofs.RE05.gaussian_product_powers_integral ι (inferInstance) k
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example : ∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1 = 0 := by
  exact @NLA.Proofs.RE05.gaussian_third_integral 
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example (t : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (x ^ 2 / 2))
      (t * Real.exp (t ^ 2 / 2)) t := by
  exact @_private.NLA.Proofs.RE05.GaussianMoments.0.NLA.Proofs.RE05.gaussian_mgf_deriv_one t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example (t : ℝ) :
    HasDerivAt (fun x : ℝ => x * Real.exp (x ^ 2 / 2))
      ((1 + t ^ 2) * Real.exp (t ^ 2 / 2)) t := by
  exact @_private.NLA.Proofs.RE05.GaussianMoments.0.NLA.Proofs.RE05.gaussian_mgf_deriv_two t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example (t : ℝ) :
    HasDerivAt (fun x : ℝ => (1 + x ^ 2) * Real.exp (x ^ 2 / 2))
      ((3 * t + t ^ 3) * Real.exp (t ^ 2 / 2)) t := by
  exact @_private.NLA.Proofs.RE05.GaussianMoments.0.NLA.Proofs.RE05.gaussian_mgf_deriv_three t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example (t : ℝ) :
    HasDerivAt (fun x : ℝ => (3 * x + x ^ 3) * Real.exp (x ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * Real.exp (t ^ 2 / 2)) t := by
  exact @_private.NLA.Proofs.RE05.GaussianMoments.0.NLA.Proofs.RE05.gaussian_mgf_deriv_four t
end NLA.Proofs.RE05
namespace NLA.Proofs.RE05
open MeasureTheory ProbabilityTheory
example : ∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  exact @NLA.Proofs.RE05.gaussian_fourth_integral 
end NLA.Proofs.RE05

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory NLA.Proofs.RE05

example : NLA.Statements.RE05.Target = NLA.ReviewedStatements.RE05.Target := rfl
example (k : ℕ) : Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) :=
  gaussian_power_integrable k
example : (∫ x : ℝ, x ∂gaussianReal 0 1) = 0 := gaussian_first_integral
example : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := gaussian_second_integral
example : (∫ x : ℝ, x ^ 3 ∂gaussianReal 0 1) = 0 := gaussian_third_integral
example : (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 1) = 3 := gaussian_fourth_integral
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    Integrable (fun x : ι → ℝ => ∏ i, x i ^ k i)
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
  gaussian_product_powers_integrable k
example {ι : Type*} [Fintype ι] (k : ι → ℕ) :
    (∫ x : ι → ℝ, ∏ i, x i ^ k i ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      ∏ i, ∫ x : ℝ, x ^ k i ∂gaussianReal 0 1 := gaussian_product_powers_integral k

-- This is the same standard Gaussian law as every original stream coordinate.
example (j : ℕ) :
    (∫ ω : ℕ → ℝ, (ω j) ^ 4
      ∂NLA.Computation.NonadaptiveMatrixQuery.GaussianLaw) = 3 := by
  have h := (measurePreserving_eval_infinitePi
    (fun _ : ℕ => gaussianReal 0 1) j).hasLaw.integral_comp
      (show AEStronglyMeasurable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) by fun_prop)
  simpa only [gaussian_fourth_integral, Function.comp_apply, Function.eval,
    NLA.Computation.NonadaptiveMatrixQuery.GaussianLaw] using h

#assert_trust kernel gaussian_power_integrable
#assert_trust kernel gaussian_first_integral
#assert_trust kernel gaussian_second_integral
#assert_trust kernel gaussian_third_integral
#assert_trust kernel gaussian_fourth_integral
#assert_trust kernel gaussian_product_powers_integrable
#assert_trust kernel gaussian_product_powers_integral
#print axioms gaussian_power_integrable
#print axioms gaussian_first_integral
#print axioms gaussian_second_integral
#print axioms gaussian_third_integral
#print axioms gaussian_fourth_integral
#print axioms gaussian_product_powers_integrable
#print axioms gaussian_product_powers_integral

end
