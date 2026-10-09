import NLA.TR07.FiniteProbability

noncomputable section
open scoped BigOperators
namespace NLA.TR07.Law
variable {α β : Type*} [Fintype α] [Fintype β]

theorem variance_le_of_diameter (p : Law α) (f : α → ℝ)
    (h : ∀ a b, |f a - f b| ≤ 1) : p.variance f ≤ 1 := by
  apply p.expect_le_const
  intro a
  have habs : |f a - p.expect f| ≤ 1 := by
    rw [← p.expect_const (f a), ← p.expect_sub]
    exact p.abs_expect_le_const (h a)
  nlinarith [sq_abs (f a - p.expect f), abs_nonneg (f a - p.expect f)]

theorem variance_iid_succ (p : Law α) (r : ℕ) (f : (Fin (r+1) → α) → ℝ) :
    (p.iid (r+1)).variance f =
      p.expect (fun a => (p.iid r).variance (fun x => f (Fin.cons a x))) +
      p.variance (fun a => (p.iid r).expect (fun x => f (Fin.cons a x))) := by
  simp_rw [variance_eq, expect_iid_succ, expect_sub]
  ring

/-- Product variance bound for a function changing by at most one in each coordinate. -/
theorem variance_iid_le (p : Law α) (r : ℕ) (f : (Fin r → α) → ℝ)
    (hLip : ∀ x i a, |f (Function.update x i a) - f x| ≤ 1) :
    (p.iid r).variance f ≤ r := by
  induction r with
  | zero =>
    simp [variance, expect_iid_zero]
  | succ r ih =>
    rw [variance_iid_succ]
    have ht : ∀ a, (p.iid r).variance (fun x => f (Fin.cons a x)) ≤ r := by
      intro a
      apply ih
      intro x i b
      simpa only [← Fin.cons_update] using hLip (Fin.cons a x) i.succ b
    have hh : p.variance (fun a => (p.iid r).expect (fun x => f (Fin.cons a x))) ≤ 1 := by
      apply p.variance_le_of_diameter
      intro a b
      rw [← expect_sub]
      apply (p.iid r).abs_expect_le_const
      intro x
      simpa only [Fin.update_cons_zero] using hLip (Fin.cons b x) 0 a
    have := p.expect_le_const ht
    push_cast
    linarith

@[simp] theorem variance_add_const (p : Law α) (f : α → ℝ) (c : ℝ) :
    p.variance (fun a => f a + c) = p.variance f := by
  simp only [variance, expect_add, expect_const, add_sub_add_right_eq_sub]

@[simp] theorem variance_const_add (p : Law α) (f : α → ℝ) (c : ℝ) :
    p.variance (fun a => c + f a) = p.variance f := by
  simpa only [add_comm] using p.variance_add_const f c

theorem variance_const_mul (p : Law α) (f : α → ℝ) (c : ℝ) :
    p.variance (fun a => c * f a) = c^2 * p.variance f := by
  simp only [variance, expect_const_mul, ← mul_sub, mul_pow]

theorem expect_iid_sum (p : Law α) (r : ℕ) (f : α → ℝ) :
    (p.iid r).expect (fun x => ∑ i, f (x i)) = r * p.expect f := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [expect_iid_succ]
    simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, expect_add, expect_const, ih]
    push_cast
    ring

theorem variance_iid_sum (p : Law α) (r : ℕ) (f : α → ℝ) :
    (p.iid r).variance (fun x => ∑ i, f (x i)) = r * p.variance f := by
  induction r with
  | zero => simp [variance]
  | succ r ih =>
    rw [variance_iid_succ]
    simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, variance_const_add, ih,
      expect_const, expect_add, expect_iid_sum]
    simp only [variance_add_const, expect_const]
    push_cast
    ring

theorem expect_iid_average (p : Law α) (r : ℕ) (hr : 0 < r) (f : α → ℝ) :
    (p.iid r).expect (fun x => (∑ i, f (x i)) / r) = p.expect f := by
  simp only [div_eq_mul_inv, expect_mul_const, expect_iid_sum]
  have h : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

theorem variance_iid_average (p : Law α) (r : ℕ) (hr : 0 < r) (f : α → ℝ) :
    (p.iid r).variance (fun x => (∑ i, f (x i)) / r) = p.variance f / r := by
  simp only [div_eq_inv_mul, variance_const_mul, variance_iid_sum]
  have h : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp

end NLA.TR07.Law
