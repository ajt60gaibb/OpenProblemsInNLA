/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
Statement draft only: no graph-Jacobian inequality proof is claimed.
-/
import NLA.TR06.Definitions
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.NormDet
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.TR06

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The actual paired map into the L2 product: its squared output norm is
`‖A x‖ ^ 2 + ‖B x‖ ^ 2`, not the maximum of the two output norms. -/
def pairedL2Map (A : E →L[ℝ] F) (B : E →L[ℝ] G) :
    E →L[ℝ] WithLp 2 (F × G) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F G).symm.toContinuousLinearMap.comp (A.prod B)

/-- The graph map x ↦ (x, T x), in the genuine Hilbert product. -/
def graphL2Map (T : E →L[ℝ] F) : E →L[ℝ] WithLp 2 (E × F) :=
  pairedL2Map (ContinuousLinearMap.id ℝ E) T

/-- B after the inverse of A onto its actual range. The range norm is induced
from F. This is the same construction used by the frozen inducedDerivative. -/
def rangeInverseOperator (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hA : Function.Injective A) : LinearMap.range A.toLinearMap →L[ℝ] G :=
  B.comp (LinearEquiv.ofInjective A.toLinearMap hA).toContinuousLinearEquiv.symm.toContinuousLinearMap

-- Proposed exact theorem `opNorm_le_normDet_graphL2Map`.
-- No nonzero dimension or positive-rank premise: in dimension zero this is 0 ≤ 1.
#check (∀ T : E →L[ℝ] F, ‖T‖ ≤ (graphL2Map T).toLinearMap.normDet : Prop)

-- Proposed exact theorem `opNorm_rangeInverseOperator_mul_normDet_le`.
-- Norm determinants use the actual domain dimension and the actual Hilbert norms.
#check (∀ (A : E →L[ℝ] F) (B : E →L[ℝ] G) (hA : Function.Injective A),
  ‖rangeInverseOperator A B hA‖ * A.toLinearMap.normDet ≤
    (pairedL2Map A B).toLinearMap.normDet : Prop)

end NLA.TR06
