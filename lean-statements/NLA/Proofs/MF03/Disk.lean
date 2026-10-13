import NLA.Statements.MF03
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-! A coefficient-budget certificate for the closed complex disk in MF-03. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

open NLA.Statements.MF03

/-- Evaluation of a degree-`m` polynomial on a disk is bounded by the
radius-weighted sum of its coefficient norms. -/
theorem norm_eval_le_coeff_radius
    (P : Polynomial ℂ) (m : ℕ) (R : ℝ) (hP : P.natDegree ≤ m)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖P.eval z‖ ≤ ∑ j ∈ Finset.range (m + 1), ‖P.coeff j‖ * R ^ j := by
  rw [Polynomial.eval_eq_sum_range' (by omega : P.natDegree < m + 1)]
  calc
    ‖∑ j ∈ Finset.range (m + 1), P.coeff j * z ^ j‖ ≤
        ∑ j ∈ Finset.range (m + 1), ‖P.coeff j * z ^ j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (m + 1), ‖P.coeff j‖ * R ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz j)
        (norm_nonneg _)

/-- The nonconstant denominator coefficients control its deviation from
one on the entire closed disk. -/
theorem norm_eval_sub_one_le_tail
    (Q : Polynomial ℂ) (m : ℕ) (R : ℝ)
    (hQ : Q.natDegree ≤ m) (hQ0 : Q.coeff 0 = 1)
    (z : ℂ) (hz : ‖z‖ ≤ R) :
    ‖Q.eval z - 1‖ ≤
      ∑ j ∈ Finset.range m, ‖Q.coeff (j + 1)‖ * R ^ (j + 1) := by
  have hrepr : Q.eval z - 1 =
      ∑ j ∈ Finset.range m, Q.coeff (j + 1) * z ^ (j + 1) := by
    rw [Polynomial.eval_eq_sum_range' (by omega : Q.natDegree < m + 1)]
    rw [Finset.sum_range_succ']
    simp [hQ0]
  rw [hrepr]
  calc
    ‖∑ j ∈ Finset.range m, Q.coeff (j + 1) * z ^ (j + 1)‖ ≤
        ∑ j ∈ Finset.range m, ‖Q.coeff (j + 1) * z ^ (j + 1)‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg z) hz (j + 1)) (norm_nonneg _)

/-- A finite coefficient certificate implies the exact pole-free and
two-error bound on the full closed disk. Here the first budget omits the
constant coefficient `Q.coeff 0 = 1`. -/
theorem disk_bound_of_coefficient_tail
    (P Q : Polynomial ℂ) (m : ℕ)
    (hP : P.natDegree ≤ m) (hQ : Q.natDegree ≤ m)
    (hQ0 : Q.coeff 0 = 1)
    (hT : (∑ j ∈ Finset.range m,
      ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)) < 1)
    (hN : (∑ j ∈ Finset.range (m + 1),
      ‖P.coeff j - Q.coeff j‖ * (3 : ℝ) ^ j) ≤
        2 * (1 - ∑ j ∈ Finset.range m,
          ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1))) :
    ∀ z : ℂ, ‖z‖ ≤ (3 : ℝ) →
      Q.eval z ≠ 0 ∧ ‖(1 : ℂ) - P.eval z / Q.eval z‖ ≤ (2 : ℝ) := by
  intro z hz
  let T : ℝ := ∑ j ∈ Finset.range m,
    ‖Q.coeff (j + 1)‖ * (3 : ℝ) ^ (j + 1)
  let N : ℝ := ∑ j ∈ Finset.range (m + 1),
    ‖P.coeff j - Q.coeff j‖ * (3 : ℝ) ^ j
  have htail : ‖Q.eval z - 1‖ ≤ T :=
    norm_eval_sub_one_le_tail Q m 3 hQ hQ0 z hz
  have hden : 1 - T ≤ ‖Q.eval z‖ := by
    have htriangle : (1 : ℝ) ≤ ‖Q.eval z‖ + ‖Q.eval z - 1‖ := by
      have h := norm_sub_le (Q.eval z) (Q.eval z - 1)
      convert h using 1
      norm_num
    linarith
  have hdenpos : 0 < ‖Q.eval z‖ := by
    linarith
  have hQne : Q.eval z ≠ 0 := by
    exact (norm_pos_iff.mp hdenpos)
  refine ⟨hQne, ?_⟩
  have hdiff : ‖P.eval z - Q.eval z‖ ≤ N := by
    have hdeg : (P - Q).natDegree ≤ m :=
      (Polynomial.natDegree_sub_le P Q).trans (max_le hP hQ)
    have hbound := norm_eval_le_coeff_radius (P - Q) m 3 hdeg z hz
    simpa only [Polynomial.eval_sub, Polynomial.coeff_sub] using hbound
  have hfrac : (1 : ℂ) - P.eval z / Q.eval z =
      (Q.eval z - P.eval z) / Q.eval z := by
    field_simp [hQne]
  rw [hfrac, norm_div]
  rw [show Q.eval z - P.eval z = -(P.eval z - Q.eval z) by ring,
    norm_neg]
  apply (div_le_iff₀ hdenpos).2
  have hN' : N ≤ 2 * (1 - T) := hN
  nlinarith

#print axioms norm_eval_le_coeff_radius
#assert_trust kernel norm_eval_le_coeff_radius
#print axioms norm_eval_sub_one_le_tail
#assert_trust kernel norm_eval_sub_one_le_tail
#print axioms disk_bound_of_coefficient_tail
#assert_trust kernel disk_bound_of_coefficient_tail

end NLA.Proofs.MF03
