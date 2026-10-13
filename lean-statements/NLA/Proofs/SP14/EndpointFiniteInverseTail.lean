import NLA.Proofs.SP14.EndpointFiniteInverseTruncation

/-!
The exact tail inequality for finite triangular inverse polynomials in
probability-Haar `L²`. Completion of the inverse remains separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem endpointFiniteInverseAddCircle_sub (r : ℝ)
    (y z : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseAddCircle r (y - z) N =
      endpointFiniteInverseAddCircle r y N -
        endpointFiniteInverseAddCircle r z N := by
  ext θ
  change endpointFiniteInverse r (y - z) N (AddCircle.toCircle θ) =
    endpointFiniteInverse r y N (AddCircle.toCircle θ) -
      endpointFiniteInverse r z N (AddCircle.toCircle θ)
  unfold endpointFiniteInverse
  simp only [physicalCoeff, lp.coeFn_sub, Pi.sub_apply, mul_sub,
    sub_mul, Finset.sum_sub_distrib]

private theorem endpointFiniteInverseLp_sub (r : ℝ)
    (y z : SobolevCoeff r) (N : ℕ) :
    endpointFiniteInverseLp r (y - z) N =
      endpointFiniteInverseLp r y N - endpointFiniteInverseLp r z N := by
  unfold endpointFiniteInverseLp
  rw [endpointFiniteInverseAddCircle_sub]
  exact ContinuousLinearMap.map_sub _ _ _

/-- The finite inverse tail is controlled by the literal weighted input tail
with the same source constant `1 + 1/(r - 1/2)`. -/
theorem endpointFiniteInverseLp_tail_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r)
    (M N : ℕ) (hMN : M ≤ N) :
    ‖endpointFiniteInverseLp r y N - endpointFiniteInverseLp r y M‖ ≤
      endpointInverseHSBound r * ‖y - sobolevTruncation r M y‖ := by
  rw [← endpointFiniteInverseLp_truncation r y M N hMN,
    ← endpointFiniteInverseLp_sub]
  exact endpointFiniteInverseLp_norm_le r hrHalf _ N

#assert_trust kernel endpointFiniteInverseLp_tail_le
#print axioms endpointFiniteInverseLp_tail_le

end NLA.Proofs.SP14
