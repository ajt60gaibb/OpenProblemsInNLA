import NLA.TR07.FinitePaths
import NLA.TR07.FiniteVariance
import Mathlib.Data.Nat.Choose.Sum

/-! Binomial reconstruction estimators and their finite-law error bounds. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07
open Law
variable {α E : Type*} [Fintype α] [NormedAddCommGroup E] [NormedSpace ℝ E]

def trajectoryEstimator (u : α → E) (L : ℕ) (z : Fin L → α) : E :=
  ∑ j : Fin L, ((-1:ℝ)^j.val * (L.choose (j.val+1):ℝ)) • u (z j)

theorem binomial_filter_identity (T : E →ₗ[ℝ] E) (L : ℕ) (x : E) :
    (∑ j : Fin L, ((-1:ℝ)^j.val * (L.choose (j.val+1):ℝ)) • (T^(j.val+1)) x) =
      x - ((1-T)^L) x := by
  have h := congrArg (fun U : E →ₗ[ℝ] E => U x) ((Commute.one_right (-T)).add_pow L)
  have hn : -T = (-1:ℝ) • T := by simp
  rw [show -T + 1 = 1-T by abel, LinearMap.sum_apply] at h
  simp only [hn, smul_pow, one_pow, mul_one, Module.End.mul_apply, Module.End.natCast_apply,
    LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℝ, map_smul] at h
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, one_smul, Module.End.one_apply] at h
  rw [Fin.sum_univ_eq_sum_range (fun j => ((-1:ℝ)^j * (L.choose (j+1):ℝ)) • (T^(j+1)) x) L]
  have hs : (∑ j ∈ Finset.range L, (L.choose (j+1):ℝ) • ((-1:ℝ)^(j+1) • (T^(j+1)) x)) =
      -(∑ j ∈ Finset.range L, ((-1:ℝ)^j * (L.choose (j+1):ℝ)) • (T^(j+1)) x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ, smul_smul]
    module
  rw [hs] at h
  exact eq_sub_iff_add_eq.mpr (by rw [h]; abel)

theorem trajectoryEstimator_mean (K : α → Law α) (u : α → E) (T : E →ₗ[ℝ] E)
    (hmean : ∀ x, (K x).mean u = T (u x)) (L : ℕ) (x : α) :
    (Law.paths K L x).mean (trajectoryEstimator u L) = u x - ((1-T)^L) (u x) := by
  unfold trajectoryEstimator
  rw [mean_sum]
  simp_rw [mean_smul, mean_paths_coordinate K u T hmean]
  exact binomial_filter_identity T L (u x)

omit [Fintype α] in
theorem trajectoryEstimator_norm_le (u : α → E) {R : ℝ}
    (hu : ∀ a, ‖u a‖ ≤ R) (L : ℕ) (z : Fin L → α) :
    ‖trajectoryEstimator u L z‖ ≤ ((2:ℝ)^L - 1) * R := by
  have hc : (∑ j : Fin L, (L.choose (j.val+1):ℝ)) = (2:ℝ)^L - 1 := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) (Nat.sum_range_choose L)
    push_cast at h
    rw [Finset.sum_range_succ'] at h
    simp only [Nat.choose_zero_right, Nat.cast_one] at h
    rw [Fin.sum_univ_eq_sum_range (fun j => (L.choose (j+1):ℝ)) L]
    linarith
  calc
    ‖trajectoryEstimator u L z‖ ≤ ∑ j : Fin L,
        ‖((-1:ℝ)^j.val * (L.choose (j.val+1):ℝ)) • u (z j)‖ := norm_sum_le _ _
    _ = ∑ j : Fin L, (L.choose (j.val+1):ℝ) * ‖u (z j)‖ := by
      simp [norm_smul]
    _ ≤ ∑ j : Fin L, (L.choose (j.val+1):ℝ) * R :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hu _) (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.sum_mul, hc]

end NLA.TR07
