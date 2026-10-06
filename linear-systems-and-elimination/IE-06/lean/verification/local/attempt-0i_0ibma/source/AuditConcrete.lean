import Lean
import NLA.IE06.Definitions
import NLA.IE06.Elimination
import NLA.IE06.EliminationBlock
import NLA.IE06.EliminationSmoothing
import NLA.IE06.FinalAssembly
import NLA.IE06.FinalFailureScalars
import NLA.IE06.FinalGrowthScalars
import NLA.IE06.FiniteNet
import NLA.IE06.GEPP
import NLA.IE06.GaussianAdaptiveAppend
import NLA.IE06.GaussianAdaptiveFuture
import NLA.IE06.GaussianAllRows
import NLA.IE06.GaussianAppend
import NLA.IE06.GaussianCandidateRows
import NLA.IE06.GaussianCandidateStacking
import NLA.IE06.GaussianColumnSplit
import NLA.IE06.GaussianCompression
import NLA.IE06.GaussianConcentration
import NLA.IE06.GaussianConcentrationSpace
import NLA.IE06.GaussianCoordinates
import NLA.IE06.GaussianDenominator
import NLA.IE06.GaussianDeterminantMoments
import NLA.IE06.GaussianEliminationTail
import NLA.IE06.GaussianFrobenius
import NLA.IE06.GaussianFutureSmoothing
import NLA.IE06.GaussianFutureWindow
import NLA.IE06.GaussianLinear
import NLA.IE06.GaussianNull
import NLA.IE06.GaussianOperatorInverse
import NLA.IE06.GaussianOperatorNet
import NLA.IE06.GaussianOvercrowding
import NLA.IE06.GaussianOvercrowdingScalars
import NLA.IE06.GaussianOvercrowdingSpectral
import NLA.IE06.GaussianPivotConditioning
import NLA.IE06.GaussianPivotMasking
import NLA.IE06.GaussianPrefixDecomposition
import NLA.IE06.GaussianPrincipalMoments
import NLA.IE06.GaussianPrincipalTail
import NLA.IE06.GaussianQuadratic
import NLA.IE06.GaussianRegression
import NLA.IE06.GaussianRestriction
import NLA.IE06.GaussianShift
import NLA.IE06.GaussianShiftGeometry
import NLA.IE06.GaussianSmallest
import NLA.IE06.GaussianSmoothing
import NLA.IE06.GaussianSpectralBase
import NLA.IE06.GaussianSpectralProfile
import NLA.IE06.GaussianSpectralRecursion
import NLA.IE06.GaussianSpectralTail
import NLA.IE06.GaussianStackingTail
import NLA.IE06.GaussianStageSmoothing
import NLA.IE06.GaussianTies
import NLA.IE06.GaussianTruncatedRows
import NLA.IE06.GrowthEvents
import NLA.IE06.KernelFrame
import NLA.IE06.KyFan
import NLA.IE06.Measurability
import NLA.IE06.Pivot
import NLA.IE06.PivotFiltration
import NLA.IE06.ProfileSum
import NLA.IE06.Reduction
import NLA.IE06.RightInverseBounds
import NLA.IE06.ScalarRecurrence
import NLA.IE06.SelectedBlockAppend
import NLA.IE06.SelectedBlockCandidates
import NLA.IE06.SelectedBlockElimination
import NLA.IE06.SelectedBlockExtension
import NLA.IE06.SelectedBlockExtensionCore
import NLA.IE06.SelectedBlockExtensionScalars
import NLA.IE06.SelectedBlockTruncation
import NLA.IE06.Semantics
import NLA.IE06.Spectral
import NLA.IE06.SpectralMeasurability
import NLA.IE06.SpectralRecursionScalars
import NLA.IE06.SpectralStacking
import NLA.IE06.Statements
import NLA.IE06.SubGaussianQuadratic
import NLA.IE06.TruncatedInverse
import NLA.IE06.Unconditional
import NLA.IE06.Vendor.Isoperimetric.Basic
import NLA.IE06.Vendor.Isoperimetric.PrekopaLeindler
import NLA.IE06.Vendor.SLT.ConvergenceL1Subseq
import NLA.IE06.Vendor.SLT.EfronStein
import NLA.IE06.Vendor.SLT.GaussianLSI.BernoulliLSI
import NLA.IE06.Vendor.SLT.GaussianLSI.DualEntApp
import NLA.IE06.Vendor.SLT.GaussianLSI.DualityEntropy
import NLA.IE06.Vendor.SLT.GaussianLSI.Entropy
import NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSI
import NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSICompSmo
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Basic
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Decomposition
import NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Subadditivity
import NLA.IE06.Vendor.SLT.GaussianLSI.TensorizedGLSI
import NLA.IE06.Vendor.SLT.GaussianLSI.TwoPoint
import NLA.IE06.Vendor.SLT.GaussianLipConcen
import NLA.IE06.Vendor.SLT.GaussianMeasure
import NLA.IE06.Vendor.SLT.GaussianPoincare.EfronSteinApp
import NLA.IE06.Vendor.SLT.GaussianPoincare.LevyContinuity
import NLA.IE06.Vendor.SLT.GaussianPoincare.Limit
import NLA.IE06.Vendor.SLT.GaussianPoincare.RademacherApprox
import NLA.IE06.Vendor.SLT.GaussianPoincare.TaylorBound
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Cutoff
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Defs
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Density
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.LipschitzMollification
import NLA.IE06.Vendor.SLT.GaussianSobolevDense.Mollification
import NLA.IE06.Vendor.SLT.LipschitzProperty
import NLA.IE06.Vendor.SLT.MatrixInfra.Basic
import NLA.IE06.Vendor.SLT.MatrixInfra.CourantFischer
import NLA.IE06.Vendor.SLT.MeasureInfrastructure
import KernelControl
import NLA
import Solution

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let localModules : Array Name := #[`NLA.IE06.Definitions, `NLA.IE06.Elimination, `NLA.IE06.EliminationBlock, `NLA.IE06.EliminationSmoothing, `NLA.IE06.FinalAssembly, `NLA.IE06.FinalFailureScalars, `NLA.IE06.FinalGrowthScalars, `NLA.IE06.FiniteNet, `NLA.IE06.GEPP, `NLA.IE06.GaussianAdaptiveAppend, `NLA.IE06.GaussianAdaptiveFuture, `NLA.IE06.GaussianAllRows, `NLA.IE06.GaussianAppend, `NLA.IE06.GaussianCandidateRows, `NLA.IE06.GaussianCandidateStacking, `NLA.IE06.GaussianColumnSplit, `NLA.IE06.GaussianCompression, `NLA.IE06.GaussianConcentration, `NLA.IE06.GaussianConcentrationSpace, `NLA.IE06.GaussianCoordinates, `NLA.IE06.GaussianDenominator, `NLA.IE06.GaussianDeterminantMoments, `NLA.IE06.GaussianEliminationTail, `NLA.IE06.GaussianFrobenius, `NLA.IE06.GaussianFutureSmoothing, `NLA.IE06.GaussianFutureWindow, `NLA.IE06.GaussianLinear, `NLA.IE06.GaussianNull, `NLA.IE06.GaussianOperatorInverse, `NLA.IE06.GaussianOperatorNet, `NLA.IE06.GaussianOvercrowding, `NLA.IE06.GaussianOvercrowdingScalars, `NLA.IE06.GaussianOvercrowdingSpectral, `NLA.IE06.GaussianPivotConditioning, `NLA.IE06.GaussianPivotMasking, `NLA.IE06.GaussianPrefixDecomposition, `NLA.IE06.GaussianPrincipalMoments, `NLA.IE06.GaussianPrincipalTail, `NLA.IE06.GaussianQuadratic, `NLA.IE06.GaussianRegression, `NLA.IE06.GaussianRestriction, `NLA.IE06.GaussianShift, `NLA.IE06.GaussianShiftGeometry, `NLA.IE06.GaussianSmallest, `NLA.IE06.GaussianSmoothing, `NLA.IE06.GaussianSpectralBase, `NLA.IE06.GaussianSpectralProfile, `NLA.IE06.GaussianSpectralRecursion, `NLA.IE06.GaussianSpectralTail, `NLA.IE06.GaussianStackingTail, `NLA.IE06.GaussianStageSmoothing, `NLA.IE06.GaussianTies, `NLA.IE06.GaussianTruncatedRows, `NLA.IE06.GrowthEvents, `NLA.IE06.KernelFrame, `NLA.IE06.KyFan, `NLA.IE06.Measurability, `NLA.IE06.Pivot, `NLA.IE06.PivotFiltration, `NLA.IE06.ProfileSum, `NLA.IE06.Reduction, `NLA.IE06.RightInverseBounds, `NLA.IE06.ScalarRecurrence, `NLA.IE06.SelectedBlockAppend, `NLA.IE06.SelectedBlockCandidates, `NLA.IE06.SelectedBlockElimination, `NLA.IE06.SelectedBlockExtension, `NLA.IE06.SelectedBlockExtensionCore, `NLA.IE06.SelectedBlockExtensionScalars, `NLA.IE06.SelectedBlockTruncation, `NLA.IE06.Semantics, `NLA.IE06.Spectral, `NLA.IE06.SpectralMeasurability, `NLA.IE06.SpectralRecursionScalars, `NLA.IE06.SpectralStacking, `NLA.IE06.Statements, `NLA.IE06.SubGaussianQuadratic, `NLA.IE06.TruncatedInverse, `NLA.IE06.Unconditional, `NLA.IE06.Vendor.Isoperimetric.Basic, `NLA.IE06.Vendor.Isoperimetric.PrekopaLeindler, `NLA.IE06.Vendor.SLT.ConvergenceL1Subseq, `NLA.IE06.Vendor.SLT.EfronStein, `NLA.IE06.Vendor.SLT.GaussianLSI.BernoulliLSI, `NLA.IE06.Vendor.SLT.GaussianLSI.DualEntApp, `NLA.IE06.Vendor.SLT.GaussianLSI.DualityEntropy, `NLA.IE06.Vendor.SLT.GaussianLSI.Entropy, `NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSI, `NLA.IE06.Vendor.SLT.GaussianLSI.OneDimGLSICompSmo, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Basic, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Decomposition, `NLA.IE06.Vendor.SLT.GaussianLSI.SubAddEnt.Subadditivity, `NLA.IE06.Vendor.SLT.GaussianLSI.TensorizedGLSI, `NLA.IE06.Vendor.SLT.GaussianLSI.TwoPoint, `NLA.IE06.Vendor.SLT.GaussianLipConcen, `NLA.IE06.Vendor.SLT.GaussianMeasure, `NLA.IE06.Vendor.SLT.GaussianPoincare.EfronSteinApp, `NLA.IE06.Vendor.SLT.GaussianPoincare.LevyContinuity, `NLA.IE06.Vendor.SLT.GaussianPoincare.Limit, `NLA.IE06.Vendor.SLT.GaussianPoincare.RademacherApprox, `NLA.IE06.Vendor.SLT.GaussianPoincare.TaylorBound, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Cutoff, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Defs, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Density, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.LipschitzMollification, `NLA.IE06.Vendor.SLT.GaussianSobolevDense.Mollification, `NLA.IE06.Vendor.SLT.LipschitzProperty, `NLA.IE06.Vendor.SLT.MatrixInfra.Basic, `NLA.IE06.Vendor.SLT.MatrixInfra.CourantFischer, `NLA.IE06.Vendor.SLT.MeasureInfrastructure, `KernelControl, `NLA, `Solution]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some moduleName := env.header.moduleNames[idx.toNat]? | continue
    if localModules.contains moduleName then
      let axioms ← liftCoreM <| collectAxioms name
      for axiomName in axioms do
        unless allowed.contains axiomName do
          throwError "local declaration {name} uses prohibited axiom {axiomName}"
      checked := checked + 1
  logInfo m!"All {checked} concrete local declarations have permitted transitive axioms."
