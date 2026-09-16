/-
Independent statement environment for MF-12. Every deliberate placeholder is
only a proposed proof obligation. Solution must never import this file.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Caltech's Department of Computing and
Mathematical Sciences. Apache 2.0; AI-assisted; no contact email.
-/
import NLA.MF12.Definitions

set_option autoImplicit false
open scoped BigOperators Classical Topology
open Filter

namespace NLA.MF12

theorem family_growth_is_maximum {d : ℕ} (M : Finset (Square d))
    (hM : M.Nonempty) (n : ℕ) :
    (wordNorms M n).Finite ∧ (wordNorms M n).Nonempty ∧
    (∃ w : List (Square d), w.length = n ∧ (∀ A ∈ w, A ∈ M) ∧
      spectralNorm (matrixProduct w) = familyGrowth M n) ∧
    ∀ w : List (Square d), w.length = n → (∀ A ∈ w, A ∈ M) →
      spectralNorm (matrixProduct w) ≤ familyGrowth M n := by sorry

theorem pair_word_norms {d : ℕ} (A P : Square d) (n : ℕ) :
    wordNorms (pairFamily A P) n =
      {r | ∃ w : List Bool, w.length = n ∧ r = spectralNorm (binaryProduct A P w)} := by sorry

theorem entry_maximum_norm_comparison (d : ℕ) (hd : 1 ≤ d) (A : Square d) :
    (∃ r s : Fin d, |A r s| = entryMax A) ∧
    (∀ r s : Fin d, |A r s| ≤ entryMax A) ∧
    0 ≤ entryMax A ∧ entryMax A ≤ spectralNorm A ∧
    spectralNorm A ≤ (d : ℝ) * entryMax A := by sorry

theorem tensor_norm_comparison (d e : ℕ) (hd : 1 ≤ d) (he : 1 ≤ e)
    (A : Square d) (B : Square e) :
    entryMax (tensor A B) = entryMax A * entryMax B ∧
    spectralNorm A * spectralNorm B / ((d : ℝ) * (e : ℝ)) ≤ spectralNorm (tensor A B) ∧
    spectralNorm (tensor A B) ≤ ((d : ℝ) * (e : ℝ)) * spectralNorm A * spectralNorm B := by sorry

theorem tensor_word_identity {d e : ℕ} (A P : Square d) (J : Square e)
    (w : List Bool) :
    binaryProduct (tensor A J) (tensor P J) w =
      tensor (binaryProduct A P w) (J ^ w.length) := by sorry

theorem fractional_parameters (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    0 < baseLambda ∧ baseLambda < baseMu α ∧ baseMu α < 1 ∧
    1 ≤ fractionalPowerBound α ∧
    0 < fractionalLower α ∧ fractionalLower α ≤ fractionalUpper α := by sorry

theorem fractional_projection (α : ℝ) :
    sourceU * sourceV = (1 : Square 2) ∧ resetMatrix ^ 2 = resetMatrix ∧
    fractionalMatrix α ≠ resetMatrix := by sorry

theorem jordan_two_power (t : ℝ) (q : ℕ) :
    jordanTwo t ^ q = t ^ q • (!![1, (q : ℝ); 0, 1] : Square 2) := by sorry

theorem compressed_powers (α : ℝ) (q : ℕ) :
    compressed α q = !![1 - loss q, gain α q; 0, 1] := by sorry

theorem loss_gain_bounds (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    loss 0 = 0 ∧ gain α 0 = 0 ∧
    (∀ q : ℕ, 1 ≤ q → 0 < loss q ∧ loss q ≤ 1 / 4) ∧
    ∀ q : ℕ, gain α q = Real.rpow (q : ℝ) α * Real.rpow (loss q) (1 - α) := by sorry

theorem telescoping_budget (qs : List ℕ) :
    0 ≤ diagonalBudget qs ∧ diagonalBudget qs ≤ 1 ∧
    (∀ i : ℕ, i < qs.length → 0 ≤ tailWeight qs i ∧ tailWeight qs i ≤ 1) ∧
    (∑ i ∈ Finset.range qs.length, loss (qs.getD i 0) * tailWeight qs i) =
      1 - diagonalBudget qs := by sorry

theorem compressed_product_formula (α : ℝ) (qs : List ℕ) :
    compressedProduct α qs = !![diagonalBudget qs, offDiagonalBudget α qs; 0, 1] := by sorry

theorem compressed_product_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (qs : List ℕ) :
    0 ≤ offDiagonalBudget α qs ∧
    offDiagonalBudget α qs ≤ Real.rpow (qs.sum : ℝ) α := by sorry

theorem fractional_powers_entry_bound (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (q : ℕ) (r s : Fin 6) :
    |(fractionalMatrix α ^ q) r s| ≤ fractionalPowerBound α := by sorry

theorem gap_decomposition (w : List Bool) :
    ∃ qs : List ℕ, qs ≠ [] ∧ gapWord qs = w ∧
      qs.sum + (qs.length - 1) = w.length := by sorry

theorem reset_product_factorization (α : ℝ) (q₀ qlast : ℕ) (qs : List ℕ) :
    binaryProduct (fractionalMatrix α) resetMatrix (gapWord (q₀ :: (qs ++ [qlast]))) =
      fractionalMatrix α ^ qlast * sourceV * compressedProduct α qs *
        sourceU * fractionalMatrix α ^ q₀ := by sorry

theorem fractional_all_word_upper (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (w : List Bool) (hw : 1 ≤ w.length) :
    spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix w) ≤
      fractionalUpper α * Real.rpow (w.length : ℝ) α := by sorry

theorem logarithmic_gap_bounds (n : ℕ) (hn : 4 ≤ n) :
    1 ≤ chosenGap n ∧ 1 ≤ chosenCount n ∧
    4 ^ chosenGap n ≤ n ∧ n < 4 ^ (chosenGap n + 1) ∧
    2 * (chosenGap n + 1) ≤ 4 ^ chosenGap n ∧
    chosenRemainder n + chosenCount n * (chosenGap n + 1) = n ∧
    (1 / 4 : ℝ) ≤ (chosenCount n : ℝ) * loss (chosenGap n) := by sorry

theorem bernoulli_loss (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell < 1) (k : ℕ) :
    (1 - ell) ^ k ≤ 1 / (1 + (k : ℝ) * ell) ∧
    ((1 / 4 : ℝ) ≤ (k : ℝ) * ell → (1 / 5 : ℝ) ≤ 1 - (1 - ell) ^ k) := by sorry

theorem lower_word_exact (α : ℝ) (n : ℕ) :
    (lowerWord n).length = n ∧
    binaryProduct (fractionalMatrix α) resetMatrix (lowerWord n) =
      if n < 4 then fractionalMatrix α ^ n else
        fractionalMatrix α ^ chosenRemainder n *
          (resetMatrix * fractionalMatrix α ^ chosenGap n) ^ chosenCount n := by sorry

theorem fractional_lower_all_lengths (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    fractionalLower α * Real.rpow (n : ℝ) α ≤
      spectralNorm (binaryProduct (fractionalMatrix α) resetMatrix (lowerWord n)) := by sorry

theorem fractional_growth_estimates (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (n : ℕ) (hn : 1 ≤ n) :
    fractionalLower α * Real.rpow (n : ℝ) α ≤
      familyGrowth (pairFamily (fractionalMatrix α) resetMatrix) n ∧
    familyGrowth (pairFamily (fractionalMatrix α) resetMatrix) n ≤
      fractionalUpper α * Real.rpow (n : ℝ) α := by sorry

theorem roots_of_polynomial_growth (g : ℕ → ℝ) (γ c C : ℝ)
    (hγ : 0 ≤ γ) (hc : 0 < c) (hC : 0 < C)
    (hg : ∀ n : ℕ, 1 ≤ n →
      c * Real.rpow (n : ℝ) γ ≤ g n ∧ g n ≤ C * Real.rpow (n : ℝ) γ) :
    Tendsto (fun n : ℕ => Real.rpow (g n) (1 / (n : ℝ))) atTop (𝓝 1) := by sorry

theorem jordan_entries (m n : ℕ) (r s : Fin (m + 1)) :
    (jordanMatrix m ^ n) r s =
      if r.val ≤ s.val then (Nat.choose n (s.val - r.val) : ℝ) else 0 := by sorry

theorem jordan_growth_estimates (m : ℕ) :
    0 < jordanLower m ∧ jordanMatrix m ≠ 0 ∧
    ∀ n : ℕ, 1 ≤ n →
      jordanLower m * (n : ℝ) ^ m ≤ spectralNorm (jordanMatrix m ^ n) ∧
      spectralNorm (jordanMatrix m ^ n) ≤ ((m + 1 : ℕ) : ℝ) * (n : ℝ) ^ m := by sorry

theorem integer_family_growth (m : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth (pairFamily (jordanMatrix m) 0) n = spectralNorm (jordanMatrix m ^ n) := by sorry

theorem fractional_tensor_growth (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (m : ℕ) :
    liftedA α m ≠ liftedP m ∧ 0 < liftedLower α m ∧ liftedLower α m ≤ liftedUpper α m ∧
    ∀ n : ℕ, 1 ≤ n →
      liftedLower α m * Real.rpow (n : ℝ) (α + (m : ℝ)) ≤
        familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ∧
      familyGrowth (pairFamily (liftedA α m) (liftedP m)) n ≤
        liftedUpper α m * Real.rpow (n : ℝ) (α + (m : ℝ)) := by sorry

/-- Complete original every-real-exponent finite-family target. -/
theorem realizes_every_nonnegative_exponent (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ d : ℕ, 1 ≤ d ∧ ∃ M : Finset (Square d), M.Nonempty ∧ M.card = 2 ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        (∀ n : ℕ, 1 ≤ n →
          c * Real.rpow (n : ℝ) γ ≤ familyGrowth M n ∧
          familyGrowth M n ≤ C * Real.rpow (n : ℝ) γ) ∧
        Tendsto (fun n : ℕ => Real.rpow (familyGrowth M n) (1 / (n : ℝ))) atTop (𝓝 1) := by sorry

end NLA.MF12
