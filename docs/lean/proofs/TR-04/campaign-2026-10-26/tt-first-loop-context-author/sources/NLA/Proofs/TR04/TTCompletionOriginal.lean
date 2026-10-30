import NLA.Proofs.TR04.TensorCompressionOriginal
import NLA.Proofs.TR04.TTCompletionBound
import NLA.Proofs.TR04.Optimum

/-! Ordinary TT-SVD completion transported to the immutable original tensor,
unfolding-rank and attained-optimum definitions. This supplies the ordinary
non-strict factor; TR-04's strict improvement is a separate remaining result. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.TR04.TensorFormat

def OriginalCompletion (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A X : NLA.Computation.TensorTrainApproximation.Tensor S) : Prop :=
  Completion (modeList S.mode) (originalRanks S r)
    (originalTensorLinearEquiv S A) (originalTensorLinearEquiv S X)

theorem original_completion_exists (S : NLA.Computation.TensorTrainApproximation.Shape)
    (r : NLA.Computation.TensorTrainApproximation.Ranks S)
    (A : NLA.Computation.TensorTrainApproximation.Tensor S) :
    ∃ X, OriginalCompletion S r A X := by
  obtain ⟨X, hX⟩ := completion_exists (modeList S.mode) (originalRanks S r)
    (originalTensorLinearEquiv S A)
  refine ⟨(originalTensorLinearEquiv S).symm X, ?_⟩
  simpa only [OriginalCompletion, LinearEquiv.apply_symm_apply] using hX

theorem original_completion_feasible {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X) : NLA.Computation.TensorTrainApproximation.Feasible S r X :=
  (original_feasible_iff S r X).mpr (completion_feasible h)

theorem original_completion_comparator_bound {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X) (Y : NLA.Computation.TensorTrainApproximation.Tensor S)
    (hY : NLA.Computation.TensorTrainApproximation.Feasible S r Y) :
    NLA.Computation.TensorTrainApproximation.FrobeniusSq S A X ≤
      ((S.order - 1 : ℕ) : ℝ) * NLA.Computation.TensorTrainApproximation.FrobeniusSq S A Y := by
  rw [original_error_eq, original_error_eq]
  simpa only [length_modeList] using completion_comparator_bound h
    (originalTensorLinearEquiv S Y) ((original_feasible_iff S r Y).mp hY)

theorem original_completion_optimum_bound {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X) :
    NLA.Computation.TensorTrainApproximation.FrobeniusSq S A X ≤
      ((S.order - 1 : ℕ) : ℝ) * NLA.Computation.TensorTrainApproximation.Optimum S r A := by
  obtain ⟨Y, hY, hopt⟩ := NLA.Proofs.TR04.exists_optimum S r A
  rw [hopt]
  exact original_completion_comparator_bound h Y hY

theorem original_completion_exact_of_optimum_zero
    {S : NLA.Computation.TensorTrainApproximation.Shape}
    {r : NLA.Computation.TensorTrainApproximation.Ranks S}
    {A X : NLA.Computation.TensorTrainApproximation.Tensor S}
    (h : OriginalCompletion S r A X)
    (hzero : NLA.Computation.TensorTrainApproximation.Optimum S r A = 0) : X = A := by
  have hbound := original_completion_optimum_bound h
  rw [hzero, mul_zero] at hbound
  apply (NLA.Proofs.TR04.frobeniusSq_eq_zero_iff S A X).mp
  exact le_antisymm hbound (NLA.Proofs.TR04.frobeniusSq_nonneg S A X)

#assert_trust kernel original_completion_exists
#assert_trust kernel original_completion_feasible
#assert_trust kernel original_completion_comparator_bound
#assert_trust kernel original_completion_optimum_bound
#assert_trust kernel original_completion_exact_of_optimum_zero
#print axioms original_completion_optimum_bound
#print axioms original_completion_exact_of_optimum_zero
end NLA.Proofs.TR04.TensorFormat
