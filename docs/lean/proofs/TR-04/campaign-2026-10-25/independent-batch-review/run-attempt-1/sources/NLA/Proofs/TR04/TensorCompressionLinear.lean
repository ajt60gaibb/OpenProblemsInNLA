import NLA.Proofs.TR04.TensorCompressionMerge

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators

namespace NLA.Proofs.TR04.TensorFormat

/-- The actual finite contraction/lifting action as a linear map. -/
def actFirstLinearMap {m k : ℕ} (ns : List ℕ) (M : Matrix (Fin k) (Fin m) ℝ) :
    Tensor (m :: ns) →ₗ[ℝ] Tensor (k :: ns) where
  toFun := actFirst M
  map_add' A B := by
    funext x
    simp only [actFirst, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    funext x
    simp only [actFirst, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def actFirstContinuousLinearMap {m k : ℕ} (ns : List ℕ) (M : Matrix (Fin k) (Fin m) ℝ) :
    Tensor (m :: ns) →L[ℝ] Tensor (k :: ns) :=
  (actFirstLinearMap ns M).toContinuousLinearMap

theorem continuous_actFirst {m k : ℕ} (ns : List ℕ) (M : Matrix (Fin k) (Fin m) ℝ) :
    Continuous (actFirst (ns := ns) M) := (actFirstContinuousLinearMap ns M).continuous

def unfoldContinuousLinearEquiv (ns : List ℕ) (k : ℕ) :
    Tensor ns ≃L[ℝ] Matrix (Index (ns.take k)) (Index (ns.drop k)) ℝ :=
  (unfoldLinearEquiv ns k).toContinuousLinearEquiv

def mergeContinuousLinearEquiv (k m : ℕ) (ns : List ℕ) :
    Tensor (k :: m :: ns) ≃L[ℝ] Tensor ((k * m) :: ns) :=
  (merge k m ns).toContinuousLinearEquiv

def originalTensorContinuousLinearEquiv (S : NLA.Computation.TensorTrainApproximation.Shape) :
    NLA.Computation.TensorTrainApproximation.Tensor S ≃L[ℝ] Tensor (modeList S.mode) :=
  (originalTensorLinearEquiv S).toContinuousLinearEquiv

#assert_trust kernel actFirstLinearMap
#assert_trust kernel actFirstContinuousLinearMap
#assert_trust kernel continuous_actFirst
#assert_trust kernel unfoldContinuousLinearEquiv
#assert_trust kernel mergeContinuousLinearEquiv
#assert_trust kernel originalTensorContinuousLinearEquiv
#print axioms continuous_actFirst
end NLA.Proofs.TR04.TensorFormat
