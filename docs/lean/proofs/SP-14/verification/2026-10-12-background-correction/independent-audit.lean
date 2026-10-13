import NLA.Proofs.SP14.EndpointBackgroundCorrectionL2

set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory
open NLA.Proofs.SP14

local instance auditTwoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

example (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (s : Circle) :
    ‖finiteLaurentCorrection u v pMinus pPlus s‖ ≤
      (∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|) :=
  finiteLaurentCorrection_norm_le_coeffSum u v pMinus pPlus s

example (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r)
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (y : SobolevCoeff r) :
    (∫ θ : AddCircle (2 * Real.pi),
       ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) *
         endpointInverseL2 r hrHalf y θ‖ ^ 2
         ∂AddCircle.haarAddCircle) ≤
      ((∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|)) ^ 2 *
        endpointInverseHSBound r ^ 2 * ‖y‖ ^ 2 :=
  finiteLaurentCorrection_endpointInverseL2_energy_le
    r hrHalf u v pMinus pPlus y

#assert_trust kernel finiteLaurentCorrection_norm_le_coeffSum
#assert_trust kernel finiteLaurentCorrection_endpointInverseL2_energy_le
#print axioms finiteLaurentCorrection_norm_le_coeffSum
#print axioms finiteLaurentCorrection_endpointInverseL2_energy_le
