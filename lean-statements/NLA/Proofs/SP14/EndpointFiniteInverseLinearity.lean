import NLA.Proofs.SP14.EndpointFiniteInverseParseval

/-!
Complex linearity of the actual finite triangular inverse in probability-Haar
`L²`. This is the finite algebraic prerequisite for the completed inverse.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem endpointFiniteInverseAddCircle_add (r : ℝ)
    (y z : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseAddCircle r (y + z) N =
      endpointFiniteInverseAddCircle r y N +
        endpointFiniteInverseAddCircle r z N := by
  ext θ
  change endpointFiniteInverse r (y + z) N (AddCircle.toCircle θ) =
    endpointFiniteInverse r y N (AddCircle.toCircle θ) +
      endpointFiniteInverse r z N (AddCircle.toCircle θ)
  unfold endpointFiniteInverse
  simp only [physicalCoeff, lp.coeFn_add, Pi.add_apply, mul_add,
    add_mul, Finset.sum_add_distrib]

/-- The exact finite inverse is additive as a probability-Haar `L²` class. -/
theorem endpointFiniteInverseLp_add (r : ℝ)
    (y z : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseLp r (y + z) N =
      endpointFiniteInverseLp r y N + endpointFiniteInverseLp r z N := by
  unfold endpointFiniteInverseLp
  rw [endpointFiniteInverseAddCircle_add]
  exact ContinuousLinearMap.map_add _ _ _

private theorem endpointFiniteInverseAddCircle_smul (r : ℝ)
    (c : ℂ) (y : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseAddCircle r (c • y) N =
      c • endpointFiniteInverseAddCircle r y N := by
  ext θ
  change endpointFiniteInverse r (c • y) N (AddCircle.toCircle θ) =
    c • endpointFiniteInverse r y N (AddCircle.toCircle θ)
  unfold endpointFiniteInverse
  simp only [physicalCoeff, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    mul_assoc, Finset.mul_sum]
  congr 1
  ext k
  ring

/-- The exact finite inverse commutes with complex scalar multiplication in
probability-Haar `L²`. -/
theorem endpointFiniteInverseLp_smul (r : ℝ)
    (c : ℂ) (y : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseLp r (c • y) N =
      c • endpointFiniteInverseLp r y N := by
  unfold endpointFiniteInverseLp
  rw [endpointFiniteInverseAddCircle_smul]
  exact ContinuousLinearMap.map_smul _ _ _

#assert_trust kernel endpointFiniteInverseLp_add
#print axioms endpointFiniteInverseLp_add
#assert_trust kernel endpointFiniteInverseLp_smul
#print axioms endpointFiniteInverseLp_smul

end NLA.Proofs.SP14
