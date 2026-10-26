import NLA.Proofs.PF05.CoordinateActions
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed

/-! The actual inverse pencil and its coordinate derivatives. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix Matrix.Norms.Operator Topology
open Filter

namespace NLA.Proofs.PF05
namespace CoordinateActions
noncomputable section
local instance pencilNormedRing : NormedRing M3 := Matrix.linftyOpNormedRing
local instance pencilNormedGroup : NormedAddCommGroup M3 := Matrix.linftyOpNormedAddCommGroup
local instance pencilTopology : TopologicalSpace M3 :=
  pencilNormedGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
local instance pencilNormedSpace : NormedSpace ℝ M3 := Matrix.linftyOpNormedSpace
local instance pencilNormedAlgebra : NormedAlgebra ℝ M3 := Matrix.linftyOpNormedAlgebra

/-- Actual matrix inverse, rather than a hypothetical integrated path. -/
def inversePencil (T : M3) (t : ℝ) : M3 := (1+t • T)⁻¹

theorem hasDerivAt_inversePencil (T : M3) :
    HasDerivAt (inversePencil T) (-T) 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 : M3)+t • T) T 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (1 : M3)).add
      ((hasDerivAt_id (0 : ℝ)).smul_const T) using 1; simp
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : M3ˣ)
  have hi' : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ M3 1 1) (1 : M3) := by simpa using hi
  have hcomp := (show HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℝ M3 1 1) (1+(0:ℝ) • T) by simpa using hi').comp_hasDerivAt (0 : ℝ) hl
  convert! hcomp using 1
  · funext t
    exact Matrix.nonsing_inv_eq_ringInverse (1+t • T)
  · simp [ContinuousLinearMap.mulLeftRight_apply]

private def entryCLM (i j : Fin 3) : M3 →L[ℝ] ℝ :=
  ({ toFun := fun C => C i j
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : M3 →ₗ[ℝ] ℝ).toContinuousLinearMap

theorem inversePencil_entry_derivative (T : M3) (i j : Fin 3) :
    HasDerivAt (fun t => inversePencil T t i j) (-T i j) 0 := by
  exact (entryCLM i j).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_inversePencil T)

/-- Every entry of the inverse dual pencil has the negative actual dual
operator as derivative. -/
theorem inverse_dual_entry_derivative (T : M3) (B : M2) (i j : Fin 2) :
    HasDerivAt (fun t => dual (inversePencil T t) B i j) (-dual T B i j) 0 := by
  have hv (a : Fin 3) :
      HasDerivAt (fun t => (inversePencil T t *ᵥ rightVector B) a)
        (((-T) *ᵥ rightVector B) a) 0 := by
    convert! HasDerivAt.sum (u := Finset.univ) (fun k _ =>
        (inversePencil_entry_derivative T a k).mul_const (rightVector B k)) using 1
  fin_cases i <;> fin_cases j
  · simpa [dual,decodeRight,Matrix.neg_mulVec] using hv 0
  · simpa [dual,decodeRight,Matrix.neg_mulVec,neg_div] using (hv 2).div_const 2
  · simpa [dual,decodeRight,Matrix.neg_mulVec,neg_div] using (hv 2).div_const 2
  · simpa [dual,decodeRight,Matrix.neg_mulVec] using hv 1

@[simp] theorem inverse_dual_zero (T : M3) (B : M2)
    (hs : NLA.Statements.PF05.Symmetric B) : dual (inversePencil T 0) B=B := by
  simp [inversePencil,hs]

theorem pencil_det_eventually_ne_zero (T : M3) :
    ∀ᶠ t : ℝ in 𝓝 0, (1+t • T).det ≠ 0 := by
  have hc : ContinuousAt (fun t : ℝ => (1+t • T).det) 0 := by fun_prop
  have hp : 0 < (1+(0:ℝ) • T).det := by simp
  filter_upwards [hc.eventually (lt_mem_nhds hp)] with t ht
  exact ne_of_gt ht

#assert_trust kernel hasDerivAt_inversePencil
#assert_trust kernel inverse_dual_entry_derivative
#print axioms inverse_dual_entry_derivative

end
end CoordinateActions
end NLA.Proofs.PF05
