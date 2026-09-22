import NLA.IE22.SpectralProjection
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE22
open NLA.IE21
example (θ : ℝ) (hθ : 0 < θ ∧ θ < 1)
    (m n d : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (A : Mat m n)
    (J : Space d →ₗᵢ[ℝ] Space n) :
    (∀ g : Space d, matrixMap (projectedMatrix A J) g = matrixMap A (J g)) ∧
    (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ ‖matrixRow A i‖) ∧
    deletionSingular θ A ≤ deletionSingular θ (projectedMatrix A J) := projection_semantics θ hθ m n d hn hd A J

example (m n r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r ∧ r < n)
    (A : Mat m n) (hA : UnitRows A) :
    ∃ J : Space (n - r) →ₗᵢ[ℝ] Space n,
      operatorNorm (projectedMatrix A J) ^ 2 ≤ (m : ℝ) / ((r : ℝ) + 1) ∧
      (∀ i, ‖matrixRow (projectedMatrix A J) i‖ ≤ 1) ∧
      Matrix.trace (gramMatrix (projectedMatrix A J)) ≤ m := spectral_projection m n r hm hr A hA

#print axioms matrixMap_eq_row_inner
#print axioms projected_matrixMap
#print axioms projected_row_norm_le
#print axioms projection_semantics
#print axioms orthonormalSynthesis
#print axioms gram_trace_row_norms
#print axioms spectral_projection
end NLA.IE22
