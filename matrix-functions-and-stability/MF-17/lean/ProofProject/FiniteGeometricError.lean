import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Finite geometric bounds for separated source pieces

An injective list of natural exponents has geometric sum at most `1 / (1 - ρ)`.
Both truncated subtraction directions are injective on their relevant sides
of a cut. These estimates therefore apply to arbitrary finite collections of
deleted or retained pieces, without assuming a consecutive enumeration.
-/

noncomputable section

namespace ProofProject

open Finset

/-- A finite family with distinct natural exponents is bounded by a geometric
sum. The proof enlarges a finite image to a finite range. -/
theorem sum_geometric_injOn_le {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : Set.InjOn f (s : Set ι)) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ s, ρ ^ f j) ≤ 1 / (1 - ρ) := by
  classical
  have hsub : s.image f ⊆ range (s.sup f + 1) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hk
    exact mem_range.mpr (Nat.lt_succ_of_le (le_sup hj))
  calc
    (∑ j ∈ s, ρ ^ f j) = ∑ k ∈ s.image f, ρ ^ k := by
      rw [sum_image]
      exact hf
    _ ≤ ∑ k ∈ range (s.sup f + 1), ρ ^ k :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hρ0 k)
    _ ≤ 1 / (1 - ρ) := by
      simpa only [Nat.Ico_zero_eq_range, pow_zero] using
        (geom_sum_Ico_le_of_lt_one (m := 0) (n := s.sup f + 1) hρ0 hρ1)

/-- Reverse distances to a cut stay distinct on the deleted side. -/
theorem sum_geometric_reverse_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.InjOn q (s : Set ι)) (k : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ s.filter (fun j => q j ≤ k), ρ ^ (k - q j)) ≤ 1 / (1 - ρ) := by
  apply sum_geometric_injOn_le _ _ _ hρ0 hρ1
  intro i hi j hj hij
  have hi' := mem_filter.mp hi
  have hj' := mem_filter.mp hj
  dsimp only at hij
  exact hq hi'.1 hj'.1 (by omega)

/-- Forward distances from a starting index stay distinct on the retained side. -/
theorem sum_geometric_shift_le {ι : Type*} (s : Finset ι) (q : ι → ℕ)
    (hq : Set.InjOn q (s : Set ι)) (J : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ s.filter (fun j => J ≤ q j), ρ ^ (q j - J)) ≤ 1 / (1 - ρ) := by
  apply sum_geometric_injOn_le _ _ _ hρ0 hρ1
  intro i hi j hj hij
  have hi' := mem_filter.mp hi
  have hj' := mem_filter.mp hj
  dsimp only at hij
  exact hq hi'.1 hj'.1 (by omega)

/-- Deleted indices of an injective finite enumeration. -/
theorem sum_deleted_geometric_le {n : ℕ} (q : Fin n → ℕ)
    (hq : Function.Injective q) (k : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ univ.filter (fun j => q j ≤ k), ρ ^ (k - q j)) ≤ 1 / (1 - ρ) :=
  sum_geometric_reverse_le univ q hq.injOn k hρ0 hρ1

/-- Retained indices separated from a cut by at least two original indices. -/
theorem sum_retained_geometric_le {n : ℕ} (q : Fin n → ℕ)
    (hq : Function.Injective q) (k : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ univ.filter (fun j => k + 2 ≤ q j), ρ ^ (q j - (k + 2))) ≤
      1 / (1 - ρ) :=
  sum_geometric_shift_le univ q hq.injOn (k + 2) hρ0 hρ1

/-- Remainder indices above the common initial cutoff. -/
theorem sum_remainder_geometric_le {n : ℕ} (q : Fin n → ℕ)
    (hq : Function.Injective q) (J : ℕ) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    (∑ j ∈ univ.filter (fun j => J ≤ q j), ρ ^ (q j - J)) ≤ 1 / (1 - ρ) :=
  sum_geometric_shift_le univ q hq.injOn J hρ0 hρ1

end ProofProject
