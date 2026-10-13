import NLA.Proofs.MF03.PadeDenominatorPolynomial
import NLA.Proofs.MF03.CosineTail

/-! The original coefficient-one bound for the actual complex all-order
Padé denominator polynomial. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.MF03

/-- The exact denominator coefficient hypothesis needed by the conditional
large-order disk theorem, with no changed tail, exponent, or coefficient. -/
theorem cosinePadeDenominator_coeff_norm_le_tail (m j : ℕ)
    (hjpos : 1 ≤ j) (hjm : j ≤ m) :
    ‖(cosinePadeDenominator m).coeff j‖ ≤
      (cosineTail m) ^ j := by
  let c : Fin m := ⟨j - 1, by omega⟩
  have hc : c.val + 1 = j := by
    dsimp [c]
    omega
  rw [← hc, cosinePadeDenominator_coeff_fin]
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    cosinePadeNonconstantCoeff_abs_le_tail m c

#assert_trust kernel cosinePadeDenominator_coeff_norm_le_tail
#print axioms cosinePadeDenominator_coeff_norm_le_tail

end NLA.Proofs.MF03
