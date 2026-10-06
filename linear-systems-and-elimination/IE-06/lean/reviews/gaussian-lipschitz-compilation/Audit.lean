import Lean
import NLA.IE06.Vendor.SLT.MeasureInfrastructure
import NLA.IE06.Vendor.SLT.GaussianMeasure
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Defs
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Cutoff
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Mollification
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Density
import NLA.IE06.Vendor.SLT.GaussianLSI.Entropy
import NLA.IE06.Vendor.SLT.GaussianPoincare.RademacherApprox
import NLA.IE06.Vendor.SLT.EfronStein
import NLA.IE06.Vendor.SLT.GaussianPoincare.EfronSteinApp
import NLA.IE06.Vendor.SLT.GaussianPoincare.TaylorBound
import NLA.IE06.Vendor.SLT.GaussianPoincare.LevyContinuity
import NLA.IE06.Vendor.SLT.GaussianPoincare.Limit
import NLA.IE06.Vendor.SLT.GaussianLSI.TwoPoint
import NLA.IE06.Vendor.SLT.GaussianLSI.BernoulliLSI
import NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSICompSmo
import NLA.IE06.Vendor.SLT.ConvergenceL1Subseq
import NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSI
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Basic
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Decomposition
import NLA.IE06.Vendor.SLT.GaussianLSI.DualityEntropy
import NLA.IE06.Vendor.SLT.GaussianLSI.DualEntApp
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Subadditivity
import NLA.IE06.Vendor.SLT.GaussianLSI.TensorizedGLSI
import NLA.IE06.Vendor.SLT.LipschitzProperty
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.LipschitzMollification
import NLA.IE06.Vendor.SLT.GaussianLipConcen

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[`NLA.IE06.Vendor.SLT.MeasureInfrastructure, `NLA.IE06.Vendor.SLT.GaussianMeasure, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Defs, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Cutoff, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Mollification, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Density, `NLA.IE06.Vendor.SLT.GaussianLSI.Entropy, `NLA.IE06.Vendor.SLT.GaussianPoincare.RademacherApprox, `NLA.IE06.Vendor.SLT.EfronStein, `NLA.IE06.Vendor.SLT.GaussianPoincare.EfronSteinApp, `NLA.IE06.Vendor.SLT.GaussianPoincare.TaylorBound, `NLA.IE06.Vendor.SLT.GaussianPoincare.LevyContinuity, `NLA.IE06.Vendor.SLT.GaussianPoincare.Limit, `NLA.IE06.Vendor.SLT.GaussianLSI.TwoPoint, `NLA.IE06.Vendor.SLT.GaussianLSI.BernoulliLSI, `NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSICompSmo, `NLA.IE06.Vendor.SLT.ConvergenceL1Subseq, `NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSI, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Basic, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Decomposition, `NLA.IE06.Vendor.SLT.GaussianLSI.DualityEntropy, `NLA.IE06.Vendor.SLT.GaussianLSI.DualEntApp, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Subadditivity, `NLA.IE06.Vendor.SLT.GaussianLSI.TensorizedGLSI, `NLA.IE06.Vendor.SLT.LipschitzProperty, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.LipschitzMollification, `NLA.IE06.Vendor.SLT.GaussianLipConcen]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if localModules.contains moduleName then
      let axioms ← liftCoreM <| collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "owned declaration {name} uses prohibited axiom {axiomName}"
      checked := checked + 1
  logInfo m!"All {checked} adopted Gaussian concentration declarations have permitted transitive axioms."
