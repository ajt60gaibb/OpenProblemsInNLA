import NLA.Proofs.MF03.Disk

/-! Exact rational certificate for the first MF-03 Padé order. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

private noncomputable def P₁ : Polynomial ℂ :=
  Polynomial.C 1 + Polynomial.C (5 / 12) * Polynomial.X

private noncomputable def Q₁ : Polynomial ℂ :=
  Polynomial.C 1 - Polynomial.C (1 / 12) * Polynomial.X

private theorem P₁_degree : P₁.natDegree ≤ 1 := by
  dsimp [P₁]
  compute_degree!

private theorem Q₁_degree : Q₁.natDegree ≤ 1 := by
  dsimp [Q₁]
  compute_degree!

private theorem Q₁_coeff_zero : Q₁.coeff 0 = 1 := by
  norm_num [Q₁]

private theorem P₁_Q₁_normalized : NormalizedPadeRepresentation 1 P₁ Q₁ := by
  refine ⟨P₁_degree, Q₁_degree, ?_, ?_⟩
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using Q₁_coeff_zero
  · intro j hj
    interval_cases j <;>
      norm_num [P₁, Q₁, Finset.sum_range_succ,
        Polynomial.coeff_one, Polynomial.coeff_X]

private theorem P₁_Q₁_coprime : IsCoprime P₁ Q₁ := by
  refine ⟨Polynomial.C (1 / 6), Polynomial.C (5 / 6), ?_⟩
  dsimp [P₁, Q₁]
  calc
    _ = Polynomial.C ((1 / 6 : ℂ) + 5 / 6) +
        Polynomial.C ((1 / 6 : ℂ) * (5 / 12) - (5 / 6) * (1 / 12)) *
          Polynomial.X := by
        simp only [map_add, map_sub, map_mul, map_one]
        ring
    _ = 1 := by norm_num

/-- An exact reduced normalized representation for order one. -/
theorem order_one_reduced : ReducedPadeRepresentation 1 P₁ Q₁ :=
  ⟨P₁_Q₁_normalized, P₁_Q₁_coprime⟩

/-- The order-one rational approximant obeys the sharp closed-disk bound. -/
theorem order_one_disk : ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
    Q₁.eval z ≠ 0 ∧ ‖(1 : ℂ) - P₁.eval z / Q₁.eval z‖ ≤ (2 : ℝ) := by
  apply disk_bound_of_coefficient_tail P₁ Q₁ 1 P₁_degree Q₁_degree Q₁_coeff_zero
  · norm_num [Q₁, Polynomial.coeff_one, Polynomial.coeff_X]
  · norm_num [P₁, Q₁, Finset.sum_range_succ,
      Polynomial.coeff_one, Polynomial.coeff_X]

/-- The order-one normalized Padé equations determine both polynomials. -/
theorem order_one_unique (P Q : Polynomial ℂ)
    (h : NormalizedPadeRepresentation 1 P Q) : P = P₁ ∧ Q = Q₁ := by
  obtain ⟨hP, hQ, hQzero, hcoeff⟩ := h
  have hq0 : Q.coeff 0 = 1 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hQzero
  have hp0 : P.coeff 0 = 1 := by
    have h0 := hcoeff 0 (by norm_num)
    norm_num [Finset.sum_range_succ, hq0] at h0 ⊢
    exact h0.symm
  have hq2 : Q.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hp2 : P.coeff 2 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have h1 := hcoeff 1 (by norm_num)
  have h2 := hcoeff 2 (by norm_num)
  norm_num [Finset.sum_range_succ, hq0, hq2, hp2] at h1 h2
  have hq1 : Q.coeff 1 = -(1 / 12 : ℂ) := by
    linear_combination 2 * h2
  have hp1 : P.coeff 1 = (5 / 12 : ℂ) := by
    linear_combination -h1 + hq1
  constructor
  · apply (Polynomial.ext_iff_natDegree_le hP P₁_degree).2
    intro i hi
    interval_cases i <;>
      norm_num [P₁, hp0, hp1, Polynomial.coeff_one, Polynomial.coeff_X]
  · apply (Polynomial.ext_iff_natDegree_le hQ Q₁_degree).2
    intro i hi
    interval_cases i <;>
      norm_num [Q₁, hq0, hq1, Polynomial.coeff_one, Polynomial.coeff_X]

/-- The exact MF-03 target conclusion at order one, including every
reduced normalized representative rather than a chosen pair. -/
theorem order_one_target_clause :
    (∃ P Q : Polynomial ℂ, ReducedPadeRepresentation 1 P Q) ∧
      ∀ P Q : Polynomial ℂ, ReducedPadeRepresentation 1 P Q →
        ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
          Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  refine ⟨⟨P₁, Q₁, order_one_reduced⟩, ?_⟩
  intro P Q h z hz
  obtain ⟨rfl, rfl⟩ := order_one_unique P Q h.1
  exact order_one_disk z hz

#print axioms order_one_reduced
#assert_trust kernel order_one_reduced
#print axioms order_one_disk
#assert_trust kernel order_one_disk
#print axioms order_one_unique
#assert_trust kernel order_one_unique
#print axioms order_one_target_clause
#assert_trust kernel order_one_target_clause

end NLA.Proofs.MF03
