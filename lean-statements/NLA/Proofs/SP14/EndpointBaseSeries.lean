import NLA.Proofs.SP14.BaseCoeffSummable
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
The absolutely and uniformly convergent endpoint square-root boundary
series g₀(s) = Σ aₙ s⁻ⁿ. Fourier integration is proved separately.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

/-- The normalized endpoint boundary series, whose constant term is one.
This is distinct from the odd-frequency exterior base symbol. -/
noncomputable def endpointBaseSymbol (z : Circle) : ℂ :=
  ∑' n : ℕ, baseCoeff n * (z : ℂ) ^ (-(n : ℤ))

private theorem endpointBase_term_norm (n : ℕ) (z : Circle) :
    ‖baseCoeff n * (z : ℂ) ^ (-(n : ℤ))‖ = ‖baseCoeff n‖ := by
  rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]

/-- The endpoint boundary series is absolutely convergent at every circle
point, with the same coefficient-norm majorant at every point. -/
theorem summable_endpointBase_terms (z : Circle) :
    Summable (fun n : ℕ => baseCoeff n * (z : ℂ) ^ (-(n : ℤ))) := by
  apply Summable.of_norm_bounded summable_norm_baseCoeff
  intro n
  rw [endpointBase_term_norm]

/-- Uniform absolute convergence makes the endpoint boundary symbol
continuous at every circle point. -/
theorem continuous_endpointBaseSymbol : Continuous endpointBaseSymbol := by
  unfold endpointBaseSymbol
  apply continuous_tsum
  · intro n
    have hp : Continuous (fun z : Circle => (z : Circle) ^ (-(n : ℤ))) :=
      continuous_zpow _
    have hcoe : Continuous (fun z : Circle => (z : ℂ) ^ (-(n : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro z
      exact Circle.coe_zpow z _
    exact continuous_const.mul hcoe
  · exact summable_norm_baseCoeff
  · intro n z
    rw [endpointBase_term_norm]

#assert_trust kernel summable_endpointBase_terms
#assert_trust kernel continuous_endpointBaseSymbol
#print axioms continuous_endpointBaseSymbol

end NLA.Proofs.SP14
