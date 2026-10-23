import NLA.Proofs.TR14.ContextualProductStep
import NLA.Proofs.TR14.ReducedSubalgebras

/-! The contextual one-step inequality over ℂ with the auxiliary-algebra
finiteness premise discharged by the actual finite-dimensional ambient
algebra. This is a proved generic algebra gate, not the full ordinary lower
bound or the final TR-14 target. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.TR14

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra ℂ A] [Algebra ℂ C]
  [IsReduced C] [FiniteDimensional ℂ A] [FiniteDimensional ℂ C]

/-- Actual contextual product inequality; no finiteness oracle remains. -/
theorem contextual_product_step
    (Λ : (A × C) →ₗ[ℂ] ℂ) (U V Q W : Submodule ℂ (A × C))
    (hU : (1 : A × C) ∈ U) (hV : (1 : A × C) ∈ V)
    (hFrob : ∀ a : A, (∀ b : A, Λ (a * b, 0) = 0) → a = 0)
    (hQ : ∀ b : A, ∃ x ∈ V * Q, x.1 = b)
    (hann : ∀ w ∈ W, Λ w = 0)
    (hUVQ : (U * V) * Q ≤ W) :
    Module.finrank ℂ U + Module.finrank ℂ V ≤
      Module.finrank ℂ (U * V) + Module.finrank ℂ (productStabilizer (U * V)) :=
  contextual_product_step_of_finite_reduced
    finite_reducedSubalgebras_of_finiteDimensional Λ U V Q W hU hV hFrob hQ hann hUVQ

#assert_trust kernel contextual_product_step
#print axioms contextual_product_step

end NLA.Proofs.TR14
