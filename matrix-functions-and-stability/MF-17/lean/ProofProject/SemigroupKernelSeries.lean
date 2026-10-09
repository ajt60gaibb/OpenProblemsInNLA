import ProofProject.SemigroupKernelConvolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Absolutely summable series of strong kernel operators

Summability of the scalar L¹ norms supplies both the operator-norm series and
an integrable series after applying to each vector. The interchange below uses
only vector-valued integrals, never operator-valued measurability of the orbit.
-/

noncomputable section

open MeasureTheory

namespace ProofProject.BoundedSemigroup

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem kernelOperator_neg (S : BoundedSemigroup M H)
    {k : ℝ → ℂ} (hk : Integrable k) :
    S.kernelOperator (-k) hk.neg = -S.kernelOperator k hk := by
  ext x
  simp only [kernelOperator_apply, neg_apply, Pi.neg_apply,
    neg_smul, integral_neg]

theorem summable_kernelOperator (S : BoundedSemigroup M H)
    {k : ℕ → ℝ → ℂ} (hk : ∀ n, Integrable (k n))
    (hnorm : Summable (fun n => ∫ s, ‖k n s‖)) :
    Summable (fun n => S.kernelOperator (k n) (hk n)) := by
  exact (hnorm.mul_left M).of_norm_bounded
    (fun n => S.kernelOperator_norm_le (k n) (hk n))

/-- A scalar L¹ series yields a summable sequence of vector L¹ norms. -/
theorem summable_integral_norm_kernelOrbit (S : BoundedSemigroup M H)
    {k : ℕ → ℝ → ℂ} (hk : ∀ n, Integrable (k n))
    (hnorm : Summable (fun n => ∫ s, ‖k n s‖)) (x : H) :
    Summable (fun n => ∫ s, ‖k n s • S.positiveOrbit x s‖) := by
  apply Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun s => norm_nonneg _)) _
    (hnorm.mul_right (M * ‖x‖))
  intro n
  calc
    _ ≤ ∫ s, ‖k n s‖ * (M * ‖x‖) := by
      apply integral_mono (S.kernelOrbit_integrable (hk n) x).norm
        ((hk n).norm.mul_const _)
      intro s
      change ‖k n s • S.positiveOrbit x s‖ ≤ ‖k n s‖ * (M * ‖x‖)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (S.positiveOrbit_norm_le x s) (norm_nonneg _)
    _ = _ := integral_mul_const _ _

/-- Actual kernel operators commute with a pointwise scalar series whose L¹
norms are summable. Integrability of the scalar sum remains explicit. -/
theorem kernelOperator_tsum (S : BoundedSemigroup M H)
    {k : ℕ → ℝ → ℂ} (hk : ∀ n, Integrable (k n))
    (hnorm : Summable (fun n => ∫ s, ‖k n s‖))
    (hpoint : ∀ s, Summable (fun n => k n s))
    (hsum : Integrable (fun s => ∑' n, k n s)) :
    S.kernelOperator (fun s => ∑' n, k n s) hsum =
      ∑' n, S.kernelOperator (k n) (hk n) := by
  ext x
  have heval := (ContinuousLinearMap.apply ℂ H x).map_tsum
    (S.summable_kernelOperator hk hnorm)
  change _ = (ContinuousLinearMap.apply ℂ H x) (∑' n, S.kernelOperator (k n) (hk n))
  rw [heval]
  simp only [ContinuousLinearMap.apply_apply, kernelOperator_apply]
  rw [integral_tsum_of_summable_integral_norm
    (fun n => S.kernelOrbit_integrable (hk n) x)
    (S.summable_integral_norm_kernelOrbit hk hnorm x)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => ((hpoint s).tsum_smul_const (S.positiveOrbit x s)).symm

end ProofProject.BoundedSemigroup
