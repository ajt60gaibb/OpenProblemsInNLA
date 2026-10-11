import NLA.Proofs.SP14.EndpointFiniteInverseParseval

/-!
The exact finite triangular inverse has the reviewed probability-Haar `L²`
bound. This is a finite estimate; the completed operator is a later gate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The actual finite inverse, for every `r > 1/2`, has the explicit source
bound `1 + 1/(r - 1/2)` times the literal weighted input norm. -/
theorem endpointFiniteInverseLp_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    ‖endpointFiniteInverseLp r y N‖ ≤
      endpointInverseHSBound r * ‖y‖ := by
  have hB : 0 ≤ endpointInverseHSBound r := by
    unfold endpointInverseHSBound
    have hr : 0 < r - 1 / 2 := by linarith
    positivity
  have hsq : ‖endpointFiniteInverseLp r y N‖ ^ 2 ≤
      (endpointInverseHSBound r * ‖y‖) ^ 2 := by
    calc
      ‖endpointFiniteInverseLp r y N‖ ^ 2 =
          ∑ d ∈ Finset.range N, ‖endpointFiniteInverseCoeff r y N d‖ ^ 2 :=
        endpointFiniteInverseLp_norm_sq r y N
      _ ≤ endpointInverseHSSquare r * ‖y‖ ^ 2 :=
        endpointFiniteInverse_coeff_energy_le r hrHalf y N
      _ ≤ endpointInverseHSBound r ^ 2 * ‖y‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (endpointInverseHSSquare_le r hrHalf)
          (sq_nonneg _)
      _ = (endpointInverseHSBound r * ‖y‖) ^ 2 := by ring
  have hprod : 0 ≤ endpointInverseHSBound r * ‖y‖ :=
    mul_nonneg hB (norm_nonneg _)
  nlinarith [norm_nonneg (endpointFiniteInverseLp r y N)]

#assert_trust kernel endpointFiniteInverseLp_norm_le
#print axioms endpointFiniteInverseLp_norm_le

end NLA.Proofs.SP14
