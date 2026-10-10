import NLA.Proofs.SP14.FiniteNegativeWienerMultiplier
import NLA.Proofs.SP14.NegativeLaurentEndpointDivision
import NLA.Proofs.SP14.RegularizedFactorWiener

/-!
The first literal source Wiener bound for the actual contact-corrected
negative Laurent background, retaining its finite quotient witness.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

theorem baseExterior_negativeLaurent_wiener_bound
    (u : ℕ) (p : Fin u → ℝ)
    (hcontact : negativeLaurent u p (-1 : Circle) = 0) :
  ∃ q : Fin u → ℝ,
    (∀ j : Fin u, j.val = 0 → q j = 0) ∧
    (∀ s : Circle,
      negativeLaurent u p s =
        (1 + (s : ℂ)) * negativeLaurent u q s) ∧
    Summable (fun k : ℤ =>
      wienerWeight k *
        ‖FourierCoefficient
          (fun s => baseExteriorFactor s * negativeLaurent u p s) k‖) ∧
    weightedWienerSize
      (fun s => baseExteriorFactor s * negativeLaurent u p s) ≤
      weightedWienerSize regularizedBaseFactor * finiteNegativeWienerSize u q := by
  obtain ⟨q, hqzero, hfactor⟩ := negativeLaurent_endpoint_factor u p hcontact
  have hproduct :
      (fun s : Circle => baseExteriorFactor s * negativeLaurent u p s) =
      (fun s : Circle => regularizedBaseFactor s * negativeLaurent u q s) := by
    funext s
    rw [hfactor s]
    simp [regularizedBaseFactor]
    ring
  refine ⟨q, hqzero, hfactor, ?_, ?_⟩
  · rw [hproduct]
    exact summable_mul_negativeLaurent_wiener
      regularizedBaseFactor continuous_regularizedBaseFactor
      summable_regularizedBaseFactor_wiener u q
  · rw [hproduct]
    exact weightedWienerSize_mul_negativeLaurent_le
      regularizedBaseFactor continuous_regularizedBaseFactor
      summable_regularizedBaseFactor_wiener u q

#assert_trust kernel baseExterior_negativeLaurent_wiener_bound

end NLA.Proofs.SP14
