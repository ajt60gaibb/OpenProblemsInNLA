import NLA.Proofs.SP14.BaseCoeffSummable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
The absolutely and uniformly convergent exterior-branch boundary series for
the SP-14 base symbol. Fourier integration and the square identity are proved
separately.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The normalized exterior-branch boundary series, whose leading term is
`z` because `baseCoeff 0 = 1`. -/
noncomputable def baseExteriorSymbol (z : Circle) : ℂ :=
  ∑' n : ℕ, baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ))

private theorem baseExterior_term_norm (n : ℕ) (z : Circle) :
    ‖baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ))‖ = ‖baseCoeff n‖ := by
  rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]

/-- The exterior boundary series is absolutely convergent at every circle
point, with the same coefficient-norm majorant at every point. -/
theorem summable_baseExterior_terms (z : Circle) :
    Summable (fun n : ℕ => baseCoeff n * (z : ℂ) ^ (1 - 2 * (n : ℤ))) := by
  apply Summable.of_norm_bounded summable_norm_baseCoeff
  intro n
  rw [baseExterior_term_norm]

/-- Uniform absolute convergence makes the normalized boundary symbol
continuous, including its zero points where `z² = -1`. -/
theorem continuous_baseExteriorSymbol : Continuous baseExteriorSymbol := by
  unfold baseExteriorSymbol
  apply continuous_tsum
  · intro n
    have hp : Continuous (fun z : Circle => (z : Circle) ^ (1 - 2 * (n : ℤ))) :=
      continuous_zpow _
    have hcoe : Continuous (fun z : Circle => (z : ℂ) ^ (1 - 2 * (n : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro z
      exact Circle.coe_zpow z _
    exact continuous_const.mul hcoe
  · exact summable_norm_baseCoeff
  · intro n z
    rw [baseExterior_term_norm]

#assert_trust kernel summable_baseExterior_terms
#assert_trust kernel continuous_baseExteriorSymbol
#print axioms continuous_baseExteriorSymbol

end NLA.Proofs.SP14
