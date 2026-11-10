import Mathlib
import NLA.Statements.IE22

/-! Elementary energy and extrema facts for the literal row-deletion model.
All infimum arguments use actual nonempty sets and their lower bounds. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open Set
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

def hinge (t z : ℝ) : ℝ := max (t - z ^ 2) 0

theorem hinge_nonneg (t z : ℝ) : 0 ≤ hinge t z := le_max_right _ _

theorem hinge_le {t : ℝ} (ht : 0 ≤ t) (z : ℝ) : hinge t z ≤ t := by
  exact max_le (sub_le_self _ (sq_nonneg z)) ht

theorem finite_trimming_dual_lower {ι : Type*} [Fintype ι]
    (S : Finset ι) (y : ι → ℝ) (t : ℝ) :
    (S.card : ℝ) * t - ∑ i, max (t - y i) 0 ≤ ∑ i ∈ S, y i := by
  classical
  have hselected : ∑ i ∈ S, (t - y i) ≤ ∑ i ∈ S, max (t - y i) 0 :=
    Finset.sum_le_sum (fun i _ => le_max_left _ _)
  have hall : ∑ i ∈ S, max (t - y i) 0 ≤ ∑ i, max (t - y i) 0 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => le_max_right _ _)
  have hsum : ∑ i ∈ S, (t - y i) = (S.card : ℝ) * t - ∑ i ∈ S, y i := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hsum] at hselected
  linarith

theorem retainedCount_le {θ : ℝ} (hθ : θ ≤ 1) (m : ℕ) : RetainedCount θ m ≤ m := by
  unfold RetainedCount
  have h : θ * (m : ℝ) ≤ (m : ℝ) := mul_le_of_le_one_left (Nat.cast_nonneg m) hθ
  simpa using Nat.floor_le_floor h

theorem exists_unit_vector {n : ℕ} (hn : 0 < n) :
    ∃ x : Fin n → ℝ, UnitVector x := by
  classical
  refine ⟨fun j => if j = (⟨0, hn⟩ : Fin n) then 1 else 0, ?_⟩
  simp [UnitVector]

theorem exists_retained_rows {θ : ℝ} {m : ℕ} (hθ : θ ≤ 1) :
    ∃ S : Finset (Fin m), S.card = RetainedCount θ m := by
  classical
  obtain ⟨S, _hsub, hcard⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin m))) (by simpa using retainedCount_le hθ m)
  exact ⟨S, hcard⟩

theorem energy_values_nonempty {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    {y : ℝ | ∃ S : Finset (Fin m), S.card = RetainedCount θ m ∧
      ∃ x : Fin n → ℝ, UnitVector x ∧ y = ∑ i ∈ S, (RowValue A i x) ^ 2}.Nonempty := by
  obtain ⟨S, hS⟩ := exists_retained_rows (m := m) hθ
  obtain ⟨x, hx⟩ := exists_unit_vector hn
  exact ⟨_, S, hS, x, hx, rfl⟩

theorem energy_values_bddBelow {θ : ℝ} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    BddBelow {y : ℝ | ∃ S : Finset (Fin m), S.card = RetainedCount θ m ∧
      ∃ x : Fin n → ℝ, UnitVector x ∧ y = ∑ i ∈ S, (RowValue A i x) ^ 2} := by
  refine ⟨0, ?_⟩
  rintro y ⟨S, _, x, _, rfl⟩
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem subsingularSquared_nonneg {θ : ℝ} {m n : ℕ}
    (hθ : θ ≤ 1) (hn : 0 < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    0 ≤ SubsingularSquared θ A := by
  apply le_csInf (energy_values_nonempty hθ hn A)
  rintro y ⟨S, _, x, _, rfl⟩
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem subsingularSquared_le_energy {θ : ℝ} {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (S : Finset (Fin m))
    (hS : S.card = RetainedCount θ m) (x : Fin n → ℝ) (hx : UnitVector x) :
    SubsingularSquared θ A ≤ ∑ i ∈ S, (RowValue A i x) ^ 2 := by
  exact csInf_le (energy_values_bddBelow A) ⟨S, hS, x, hx, rfl⟩

#assert_trust kernel finite_trimming_dual_lower
#assert_trust kernel retainedCount_le
#assert_trust kernel exists_unit_vector
#assert_trust kernel exists_retained_rows
#assert_trust kernel energy_values_nonempty
#assert_trust kernel energy_values_bddBelow
#assert_trust kernel subsingularSquared_nonneg
#assert_trust kernel subsingularSquared_le_energy
#print axioms finite_trimming_dual_lower
#print axioms subsingularSquared_nonneg
#print axioms subsingularSquared_le_energy
end NLA.Proofs.IE22
