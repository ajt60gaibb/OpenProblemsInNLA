import NLA.TR07.FiniteProbability
import NLA.TR07.ColumnAction

/-! Finite expectations of Euclidean vectors and exact squared-error identities. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law

variable {α β ι E : Type*} [Fintype α] [Fintype β] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

@[simp] theorem mean_const (p : Law α) (x : E) : p.mean (fun _ => x) = x := by
  simp [mean, ← Finset.sum_smul, p.sum_eq_one]

theorem mean_add (p : Law α) (f g : α → E) :
    p.mean (fun a => f a + g a) = p.mean f + p.mean g := by
  simp [mean, smul_add, Finset.sum_add_distrib]

theorem mean_sub (p : Law α) (f g : α → E) :
    p.mean (fun a => f a - g a) = p.mean f - p.mean g := by
  simp [mean, smul_sub, Finset.sum_sub_distrib]

theorem mean_smul (p : Law α) (c : ℝ) (f : α → E) :
    p.mean (fun a => c • f a) = c • p.mean f := by
  simp [mean, Finset.smul_sum, smul_smul, mul_comm]

theorem mean_sum {δ : Type*} (p : Law α) (S : Finset δ) (f : δ → α → E) :
    p.mean (fun a => ∑ i ∈ S, f i a) = ∑ i ∈ S, p.mean (f i) := by
  simp only [mean, Finset.smul_sum]
  exact Finset.sum_comm

theorem mean_linear {F : Type*} [AddCommGroup F] [Module ℝ F]
    (p : Law α) (T : E →ₗ[ℝ] F) (f : α → E) :
    p.mean (fun a => T (f a)) = T (p.mean f) := by simp [mean]

theorem norm_mean_le (p : Law α) (f : α → E) :
    ‖p.mean f‖ ≤ p.expect (fun a => ‖f a‖) := by
  calc
    _ ≤ ∑ a, ‖p.wt a • f a‖ := norm_sum_le _ _
    _ = _ := by simp [expect, norm_smul, Real.norm_of_nonneg (p.nonneg _)]

omit [Fintype ι] in
@[simp] theorem mean_apply (p : Law α) (f : α → EuclideanSpace ℝ ι) (i : ι) :
    p.mean f i = p.expect (fun a => f a i) := by simp [mean, expect]

theorem mean_bind (p : Law α) (q : α → Law β) (f : β → E) :
    (p.bind q).mean f = p.mean (fun a => (q a).mean f) := by
  simp only [mean, bind, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem mean_map (p : Law α) (g : α → β) (f : β → E) :
    (p.map g).mean f = p.mean (fun a => f (g a)) := by
  classical
  unfold map
  rw [mean_bind]
  congr 1
  funext a
  simp [mean, pure]

theorem squared_error_eq (p : Law α) (f : α → EuclideanSpace ℝ ι)
    (z : EuclideanSpace ℝ ι) :
    p.expect (fun a => ‖z - f a‖ ^ 2) =
      ‖z - p.mean f‖ ^ 2 + ∑ i, p.variance (fun a => f a i) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply]
  rw [expect_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_eq, mean_apply]
  have he (a : α) : (z i - f a i) ^ 2 = (f a i) ^ 2 - 2 * z i * f a i + (z i) ^ 2 := by ring
  simp_rw [he]
  rw [expect_add, expect_sub, expect_const_mul, expect_const]
  ring

theorem sum_variance_eq (p : Law α) (f : α → EuclideanSpace ℝ ι) :
    (∑ i, p.variance (fun a => f a i)) =
      p.expect (fun a => ‖f a‖ ^ 2) - ‖p.mean f‖ ^ 2 := by
  simp_rw [variance_eq, EuclideanSpace.real_norm_sq_eq, mean_apply]
  rw [expect_sum, Finset.sum_sub_distrib]

theorem sum_variance_le (p : Law α) (f : α → EuclideanSpace ℝ ι) :
    (∑ i, p.variance (fun a => f a i)) ≤ p.expect (fun a => ‖f a‖ ^ 2) := by
  rw [sum_variance_eq]
  linarith [sq_nonneg ‖p.mean f‖]

end NLA.TR07.Law
