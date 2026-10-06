import NLA.IE06.FinalAssembly
import NLA.IE06.GaussianSpectralProfile

/-! Complete probabilistic proof of the unchanged original IE-06 target.
Every stochastic estimate is supplied by a concrete theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.IE06

theorem schurSubpolynomialTail_proved : SchurSubpolynomialTail := by
  apply FinalAssembly.schur_tail_of_inverse_estimate
  intro β hβ
  refine ⟨GaussianSpectralProfile.profileConstant β,
    GaussianSpectralProfile.profileConstant_nonneg hβ,?_⟩
  intro n hn
  exact GaussianSpectralProfile.inverse_tail hβ hn

theorem squareRootUpperBound_proved : SquareRootUpperBound :=
  squareRootUpperBound_of_schurSubpolynomialTail_proved schurSubpolynomialTail_proved

#assert_trust kernel schurSubpolynomialTail_proved
#assert_trust kernel squareRootUpperBound_proved
#print axioms schurSubpolynomialTail_proved
#print axioms squareRootUpperBound_proved
end NLA.IE06
