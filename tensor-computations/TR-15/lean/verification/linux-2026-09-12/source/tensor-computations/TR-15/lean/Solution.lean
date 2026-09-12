import NLA.TR15.Proof

/-!
Complete formalization of Matthew J. Colbrook's TR-15 counterexample.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization; independent review is recorded separately.
-/

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.TR15

/-- Exact contraction at every real lower-order vector, including all coordinates. -/
theorem lower_contractions (x : Fin 3 → ℝ) :
    contraction witnessLower x =
      ![(x 0 + x 2) ^ 2 + (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2,
        2 * x 0 * x 1 + 4 * x 1 * x 2,
        (x 0) ^ 2 + 2 * (x 1) ^ 2 + 4 * x 0 * x 2 - (x 2) ^ 2] := by
  exact lower_contractions_proved x

/-- The full order-six contraction at the explicit nonzero higher vector. -/
theorem upper_contraction :
    contraction witnessUpper witnessUpperVector = ![0, -1] := by
  exact upper_contraction_proved

/-- Positivity of every real lower H-eigenvalue; no enumeration or existence premise. -/
theorem lower_eigenvalues_pos (eigenvalue : ℝ) (x : Fin 3 → ℝ)
    (h : IsHEigenpair witnessLower eigenvalue x) : 0 < eigenvalue := by
  exact lower_eigenvalues_pos_proved eigenvalue x h

/-- Nonvacuity, using an actual root strictly inside the specified interval. -/
theorem lower_eigenpair_exists :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ rootPolynomial t = 0 ∧
      IsHEigenpair witnessLower (lowerEigenvalue t) (lowerEigenvector t) := by
  exact lower_eigenpair_exists_proved

/-- A real negative H-eigenpair of the actual order-six tensor. -/
theorem upper_negative_eigenpair :
    IsHEigenpair witnessUpper (-1) witnessUpperVector ∧ (-1 : ℝ) < 0 := by
  exact upper_negative_eigenpair_proved

/-- A fully admissible instance with the exact original premise and failed conclusion. -/
theorem counterexample :
    Admissible 3 2 2 ∧ HasNoNegativeHEigenvalues witnessLower ∧
      ¬ HasNoNegativeHEigenvalues witnessUpper := by
  exact counterexample_proved

/-- Negation of the complete canonical universal statement. -/
theorem not_inheritanceConjecture : ¬ InheritanceConjecture := by
  exact not_inheritanceConjecture_proved

#assert_trust kernel lower_contractions
#assert_trust kernel upper_contraction
#assert_trust kernel lower_eigenvalues_pos
#assert_trust kernel lower_eigenpair_exists
#assert_trust kernel upper_negative_eigenpair
#assert_trust kernel counterexample
#assert_trust kernel not_inheritanceConjecture
#print axioms lower_contractions
#print axioms upper_contraction
#print axioms lower_eigenvalues_pos
#print axioms lower_eigenpair_exists
#print axioms upper_negative_eigenpair
#print axioms counterexample
#print axioms not_inheritanceConjecture

end NLA.TR15
