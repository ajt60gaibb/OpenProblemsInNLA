import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Splitting a finite family into initial terms and two parity classes

The initial part contains at most `J` terms. Each remaining parity class has a
canonical increasing enumeration with gaps at least two. These statements also
include empty classes and an initial cutoff beyond the whole finite family.
-/

noncomputable section

namespace ProofProject

open Finset

variable {E : Type*} [NormedAddCommGroup E]

/-- The exact finite decomposition into the omitted initial part and the two
retained parity classes. -/
theorem sum_range_eq_initial_add_parity (f : ℕ → E) (J m : ℕ) :
    (∑ q ∈ range m, f q) =
      (∑ q ∈ (range m).filter (fun q => q < J), f q) +
      (∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 0), f q) +
      (∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 1), f q) := by
  simp only [sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro q _
  by_cases hq : q < J
  · simp [hq, show ¬J ≤ q by omega]
  · have hJ : J ≤ q := by omega
    by_cases hparity : q % 2 = 0
    · simp [hq, hJ, hparity]
    · have hodd : q % 2 = 1 := by omega
      simp [hq, hJ, hodd]

/-- Uniformly bounded initial terms contribute at most `J * D`, independently
of the total number of terms. -/
theorem norm_sum_initial_le (f : ℕ → E) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ q, ‖f q‖ ≤ D) (J m : ℕ) :
    ‖∑ q ∈ (range m).filter (fun q => q < J), f q‖ ≤ (J : ℝ) * D := by
  have hsub : (range m).filter (fun q => q < J) ⊆ range J := by
    intro q hq
    exact mem_range.mpr (mem_filter.mp hq).2
  have hcard : ((range m).filter (fun q => q < J)).card ≤ J := by
    simpa only [card_range] using card_le_card hsub
  calc
    _ ≤ ∑ q ∈ (range m).filter (fun q => q < J), ‖f q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ (range m).filter (fun q => q < J), D :=
      sum_le_sum (fun q _ => hD q)
    _ = (((range m).filter (fun q => q < J)).card : ℝ) * D := by simp
    _ ≤ (J : ℝ) * D :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hD0

/-- A finite parity split with a cardinality estimate for the omitted terms. -/
theorem norm_sum_range_le_initial_add_parity (f : ℕ → E) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : ∀ q, ‖f q‖ ≤ D) (J m : ℕ) :
    ‖∑ q ∈ range m, f q‖ ≤ (J : ℝ) * D +
      ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 0), f q‖ +
      ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 1), f q‖ := by
  rw [sum_range_eq_initial_add_parity f J m]
  calc
    _ ≤ ‖∑ q ∈ (range m).filter (fun q => q < J), f q‖ +
        ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 0), f q‖ +
        ‖∑ q ∈ (range m).filter (fun q => J ≤ q ∧ q % 2 = 1), f q‖ :=
      norm_add₃_le
    _ ≤ _ := by linarith [norm_sum_initial_le f hD0 hD J m]

/-- Reindexing a finite set by its increasing enumeration preserves its sum. -/
theorem sum_orderEmbOfFin_eq (s : Finset ℕ) (f : ℕ → E) :
    (∑ i : Fin s.card, f (s.orderEmbOfFin rfl i)) = ∑ q ∈ s, f q := by
  calc
    _ = ∑ q ∈ univ.image (s.orderEmbOfFin rfl), f q := by
      rw [sum_image]
      exact (s.orderEmbOfFin rfl).injective.injOn
    _ = _ := by rw [image_orderEmbOfFin_univ]

/-- Increasing enumerations of a single parity class have gaps at least two. -/
theorem orderEmbOfFin_add_two_le {s : Finset ℕ} {p : ℕ}
    (hp : ∀ q ∈ s, q % 2 = p) {i j : Fin s.card} (hij : i < j) :
    s.orderEmbOfFin rfl i + 2 ≤ s.orderEmbOfFin rfl j := by
  have hlt := (s.orderEmbOfFin rfl).strictMono hij
  have hi := hp _ (s.orderEmbOfFin_mem rfl i)
  have hj := hp _ (s.orderEmbOfFin_mem rfl j)
  omega

end ProofProject
