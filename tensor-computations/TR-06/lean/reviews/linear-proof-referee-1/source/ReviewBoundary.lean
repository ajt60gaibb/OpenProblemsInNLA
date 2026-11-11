import NLA.TR06.AlgebraFiber
import NLA.TR06.GraphJacobian
set_option autoImplicit false
noncomputable section
namespace NLA.TR06.IndependentContributionReview

theorem character_boundary {R A K : Type*} [CommRing R] [CommRing A] [Field K]
    [Algebra R A] [Algebra R K] {N : ℕ} (g : Fin N → A)
    (hg : Submodule.span R (Set.range g) = ⊤) (q : Finset (A →ₐ[R] K)) :
    q.card ≤ N := card_algHom_finset_le_of_span_eq_top g hg q

theorem paired_norm_sq {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →L[ℝ] F) (B : E →L[ℝ] G) (x : E) :
    ‖pairedL2Map A B x‖ ^ 2 = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 (pairedL2Map A B x)

theorem rangeInverse_eq_induced {d k r : ℕ} {n : Fin d → ℕ}
    (A : EuclideanSpace ℝ (Fin k) →L[ℝ] Tensor ℝ d n)
    (B : EuclideanSpace ℝ (Fin k) →L[ℝ] AngularOutput d n r)
    (hA : Function.Injective A) :
    rangeInverseOperator A B hA = inducedDerivative A B hA := rfl

theorem graph_zero_dimension {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : EuclideanSpace ℝ (Fin 0) →L[ℝ] F) :
    ‖T‖ ≤ (graphL2Map T).toLinearMap.normDet := opNorm_le_normDet_graphL2Map T

#print axioms character_boundary
#print axioms paired_norm_sq
#print axioms rangeInverse_eq_induced
#print axioms graph_zero_dimension
#assert_trust kernel character_boundary
#assert_trust kernel paired_norm_sq
#assert_trust kernel rangeInverse_eq_induced
#assert_trust kernel graph_zero_dimension
end NLA.TR06.IndependentContributionReview
