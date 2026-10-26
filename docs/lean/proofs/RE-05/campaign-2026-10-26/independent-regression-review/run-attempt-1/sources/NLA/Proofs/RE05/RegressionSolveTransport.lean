import NLA.Proofs.RE05.RegressionBasis

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section

namespace NLA.Proofs.RE05
open NLA.Computation.LinearFamilyQuery
open scoped BigOperators Matrix InnerProductSpace

/-- Transport an actual fold-basis normal solve back to the original supplied
basis. This is valid even when either Gram is singular; it does not assert that
the two minimum-coefficient-norm selections agree in that case. -/
theorem orthonormal_solve_supplied_normal {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (c : Fin (q + 1) → ℝ)
    (hc : represent P c = represent (orthonormalMember P)
      (singleOutput (orthonormalMember P) plan responses)) :
    gram P plan *ᵥ c = rhs P plan responses := by
  ext j
  rcases represent_in_orthonormal_span P hP (Pi.single j 1) with ⟨d, hd⟩
  rw [represent_single] at hd
  have h := normal_measurement_orthogonal (orthonormalMember P) plan responses _
    (singleOutput_normal (orthonormalMember P) plan responses) d
  simp only [coefficientMeasurement_apply] at h
  rw [← hc, hd] at h
  have he : rhs P plan responses j - (gram P plan *ᵥ c) j = 0 := by
    rw [rhs_eq_measurement_inner, gram_mulVec_eq_inner, ← inner_sub_right,
      real_inner_comm]
    exact h
  exact (sub_eq_zero.mp he).symm

/-- On the explicit positive lower-tail event, the original algorithm's
actual output matrix is exactly the matrix obtained by analyzing its actual
fold basis. The basis change itself has no event premise; uniqueness uses it. -/
theorem singleOutput_matrix_basis_invariant_of_lower_bound {n q : ℕ} (P : Basis n q)
    (hP : Independent P) (plan : Plan n) (responses : List (Fin n → ℝ))
    (α : ℝ) (hα : 0 < α) (hLower : OrthonormalMeasurementLowerBound P plan α) :
    represent P (singleOutput P plan responses) =
      represent (orthonormalMember P) (singleOutput (orthonormalMember P) plan responses) := by
  rcases orthonormal_represent_in_supplied_span P hP
    (singleOutput (orthonormalMember P) plan responses) with ⟨c, hc⟩
  have hn := orthonormal_solve_supplied_normal P hP plan responses c hc
  rw [← singleOutput_unique_of_lower_bound P hP plan responses α hα hLower c hn]
  exact hc

end NLA.Proofs.RE05
