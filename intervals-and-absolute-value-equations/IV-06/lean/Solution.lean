import NLA.IV06.Proof

/-!
# IV-06: complete exports matching the independently reviewed statement boundary

The implementation imports no Challenge file. Original mathematics: Matthew J.
Colbrook. AI-assisted formalization: George Stepaniants, Department of Computing
and Mathematical Sciences, California Institute of Technology, Pasadena,
California, USA. No implementation theorem admits a placeholder.
-/

noncomputable section

namespace NLA.IV06

/-- The actual nonzero real-eigenvector and characteristic-determinant definitions agree. -/
theorem eigenvalue_determinant_semantics (n : ℕ) (A : RealMatrix n) (lam : ℝ) :
    HasRealEigenvalue A lam ↔ characteristicDet A lam = 0 := by
  exact eigenvalue_determinant_semantics_proved n A lam

/-- The original interval box is exactly the displayed two-parameter family,
and its characteristic determinant is the actual all-real polynomial. -/
theorem family_and_determinant_semantics :
    EntrywiseLE lower upper ∧
    (∀ A : RealMatrix 3, InIntervalFamily lower upper A ↔
      ∃ a b : ℝ, a ∈ Set.Icc (-166) (-16) ∧ b ∈ Set.Icc 9 159 ∧ A = family a b) ∧
    (∀ a b lam : ℝ, characteristicDet (family a b) lam =
      (lam - 25) * (lam ^ 2 - 1) - a * (lam - 1) - b * (lam + 1)) := by
  exact family_and_determinant_semantics_proved

/-- All four exact matrix-vector equations and actual attained-set memberships. -/
theorem witness_eigenpairs (i : Fin 4) :
    InIntervalFamily lower upper (family (includedA i) (includedB i)) ∧
    includedVector i ≠ 0 ∧
    (family (includedA i) (includedB i)).mulVec (includedVector i) =
      includedValue i • includedVector i ∧
    includedValue i ∈ realEigenvalueSet lower upper := by
  exact witness_eigenpairs_proved i

/-- Bounds hold for every member of the full box, and all three separators are absent. -/
theorem witness_separators :
    (∀ A : RealMatrix 3, InIntervalFamily lower upper A → ∀ j : Fin 3,
      determinantLower j ≤ characteristicDet A (separator j) ∧
      characteristicDet A (separator j) ≤ determinantUpper j) ∧
    (∀ j : Fin 3, determinantUpper j < 0) ∧
    (∀ j : Fin 3, separator j ∉ realEigenvalueSet lower upper) := by
  exact witness_separators_proved

/-- Equality of actual connected-component classes forces interval containment. -/
theorem connected_component_intervals (S : Set ℝ) (x y : S)
    (h : ConnectedComponents.mk x = ConnectedComponents.mk y) :
    Set.Icc (x : ℝ) (y : ℝ) ⊆ S := by
  exact connected_component_intervals_proved S x y h

/-- The four specified included points represent four distinct actual components. -/
theorem four_components :
    (∃ f : Fin 4 → realEigenvalueSet lower upper,
      (∀ i, (f i : ℝ) = includedValue i) ∧
      Function.Injective (fun i => ConnectedComponents.mk (f i))) ∧
    (4 : Cardinal) ≤ componentCard (realEigenvalueSet lower upper) := by
  exact four_components_proved

/-- An admissible original box in dimension three violates the claimed bound. -/
theorem counterexample :
    EntrywiseLE lower upper ∧
    (3 : Cardinal) < componentCard (realEigenvalueSet lower upper) := by
  exact counterexample_proved

/-- Full negation of the canonical all-dimension, all-real-box conjecture. -/
theorem not_componentBoundConjecture : ¬ ComponentBoundConjecture := by
  exact not_componentBoundConjecture_proved

#assert_trust kernel eigenvalue_determinant_semantics
#print axioms eigenvalue_determinant_semantics
#assert_trust kernel family_and_determinant_semantics
#print axioms family_and_determinant_semantics
#assert_trust kernel witness_eigenpairs
#print axioms witness_eigenpairs
#assert_trust kernel witness_separators
#print axioms witness_separators
#assert_trust kernel connected_component_intervals
#print axioms connected_component_intervals
#assert_trust kernel four_components
#print axioms four_components
#assert_trust kernel counterexample
#print axioms counterexample
#assert_trust kernel not_componentBoundConjecture
#print axioms not_componentBoundConjecture

end NLA.IV06
