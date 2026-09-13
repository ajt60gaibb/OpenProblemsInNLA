import NLA.IV06.Definitions

/-!
# IV-06: independent, complete statement boundary

Only this Challenge contains deliberate placeholders. It establishes no results
and must never be imported by the eventual proof or Solution environment.
Eight targets preserve the original independent-entry, real-eigenvalue and
actual connected-component semantics and end in the full universal negation.
-/

noncomputable section

namespace NLA.IV06

/-- The actual nonzero real-eigenvector and characteristic-determinant definitions agree. -/
theorem eigenvalue_determinant_semantics (n : ℕ) (A : RealMatrix n) (lam : ℝ) :
    HasRealEigenvalue A lam ↔ characteristicDet A lam = 0 := by
  sorry

/-- The original interval box is exactly the displayed two-parameter family,
and its characteristic determinant is the actual all-real polynomial. -/
theorem family_and_determinant_semantics :
    EntrywiseLE lower upper ∧
    (∀ A : RealMatrix 3, InIntervalFamily lower upper A ↔
      ∃ a b : ℝ, a ∈ Set.Icc (-166) (-16) ∧ b ∈ Set.Icc 9 159 ∧ A = family a b) ∧
    (∀ a b lam : ℝ, characteristicDet (family a b) lam =
      (lam - 25) * (lam ^ 2 - 1) - a * (lam - 1) - b * (lam + 1)) := by
  sorry

/-- All four exact matrix-vector equations and actual attained-set memberships. -/
theorem witness_eigenpairs (i : Fin 4) :
    InIntervalFamily lower upper (family (includedA i) (includedB i)) ∧
    includedVector i ≠ 0 ∧
    (family (includedA i) (includedB i)).mulVec (includedVector i) =
      includedValue i • includedVector i ∧
    includedValue i ∈ realEigenvalueSet lower upper := by
  sorry

/-- Bounds hold for every member of the full box, and all three separators are absent. -/
theorem witness_separators :
    (∀ A : RealMatrix 3, InIntervalFamily lower upper A → ∀ j : Fin 3,
      determinantLower j ≤ characteristicDet A (separator j) ∧
      characteristicDet A (separator j) ≤ determinantUpper j) ∧
    (∀ j : Fin 3, determinantUpper j < 0) ∧
    (∀ j : Fin 3, separator j ∉ realEigenvalueSet lower upper) := by
  sorry

/-- Equality of actual connected-component classes forces interval containment. -/
theorem connected_component_intervals (S : Set ℝ) (x y : S)
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    Set.Icc (x : ℝ) (y : ℝ) ⊆ S := by
  sorry

/-- The four specified included points represent four distinct actual components. -/
theorem four_components :
    (∃ f : Fin 4 → realEigenvalueSet lower upper,
      (∀ i, (f i : ℝ) = includedValue i) ∧
      Function.Injective (fun i => ConnectedComponents.mk (f i))) ∧
    (4 : Cardinal) ≤ componentCard (realEigenvalueSet lower upper) := by
  sorry

/-- An admissible original box in dimension three violates the claimed bound. -/
theorem counterexample :
    EntrywiseLE lower upper ∧
    (3 : Cardinal) < componentCard (realEigenvalueSet lower upper) := by
  sorry

/-- Full negation of the canonical all-dimension, all-real-box conjecture. -/
theorem not_componentBoundConjecture : ¬ ComponentBoundConjecture := by
  sorry

end NLA.IV06
