import NLA.Proofs.SP14.EndpointFiniteInverseNorm
import NLA.Proofs.SP14.WeightedSobolevOperators

/-!
Finite truncation compatibility for the source's actual triangular inverse.
This is an identity of finite functions and their probability-Haar `L²` classes.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

private theorem endpointFiniteInverse_truncation_pointwise (r : ℝ)
    (y : SobolevCoeff r) (M N : ℕ) (hMN : M ≤ N) (z : Circle) :
    endpointFiniteInverse r (sobolevTruncation r M y) N z =
      endpointFiniteInverse r y M z := by
  unfold endpointFiniteInverse
  simp_rw [physicalCoeff_truncation, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- Exact compatibility of the actual finite triangular inverse with the
literal first-`M` weighted-coefficient truncation, including `M=0`. -/
theorem endpointFiniteInverseLp_truncation (r : ℝ)
    (y : SobolevCoeff r) (M N : ℕ) (hMN : M ≤ N) :
    endpointFiniteInverseLp r (sobolevTruncation r M y) N =
      endpointFiniteInverseLp r y M := by
  have hcont : endpointFiniteInverseAddCircle r (sobolevTruncation r M y) N =
      endpointFiniteInverseAddCircle r y M := by
    ext θ
    exact endpointFiniteInverse_truncation_pointwise r y M N hMN _
  unfold endpointFiniteInverseLp
  rw [hcont]

#assert_trust kernel endpointFiniteInverseLp_truncation
#print axioms endpointFiniteInverseLp_truncation

end NLA.Proofs.SP14
