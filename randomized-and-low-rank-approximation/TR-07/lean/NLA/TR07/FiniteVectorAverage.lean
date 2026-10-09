import NLA.TR07.FiniteVector
import NLA.TR07.FiniteVariance

/-! Exact finite-sample averaging identities in Euclidean space. -/
noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law
variable {α ι : Type*} [Fintype α] [Fintype ι]

def average (b : ℕ) (f : α → EuclideanSpace ℝ ι) (x : Fin b → α) : EuclideanSpace ℝ ι :=
  (b : ℝ)⁻¹ • ∑ j, f (x j)

omit [Fintype α] [Fintype ι] in
theorem average_apply (b : ℕ) (f : α → EuclideanSpace ℝ ι) (x : Fin b → α) (i : ι) :
    average b f x i = (∑ j, f (x j) i) / b := by
  simp [average, div_eq_inv_mul]

omit [Fintype ι] in
theorem mean_iid_average (p : Law α) (b : ℕ) (hb : 0 < b) (f : α → EuclideanSpace ℝ ι) :
    (p.iid b).mean (average b f) = p.mean f := by
  ext i
  simp only [mean_apply, average_apply]
  exact expect_iid_average p b hb (fun a => f a i)

theorem squared_error_iid_average (p : Law α) (b : ℕ) (hb : 0 < b)
    (f : α → EuclideanSpace ℝ ι) (z : EuclideanSpace ℝ ι) :
    (p.iid b).expect (fun x => ‖z - average b f x‖ ^ 2) =
      ‖z - p.mean f‖ ^ 2 + (∑ i, p.variance (fun a => f a i)) / b := by
  rw [squared_error_eq, mean_iid_average p b hb]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [average_apply] using variance_iid_average p b hb (fun a => f a i)

theorem squared_error_iid_average_le (p : Law α) (b : ℕ) (hb : 0 < b)
    (f : α → EuclideanSpace ℝ ι) (z : EuclideanSpace ℝ ι) :
    (p.iid b).expect (fun x => ‖z - average b f x‖ ^ 2) ≤
      ‖z - p.mean f‖ ^ 2 + p.expect (fun a => ‖f a‖ ^ 2) / b := by
  rw [squared_error_iid_average p b hb]
  exact add_le_add_right (div_le_div_of_nonneg_right (sum_variance_le p f) (Nat.cast_nonneg b)) _

end NLA.TR07.Law
