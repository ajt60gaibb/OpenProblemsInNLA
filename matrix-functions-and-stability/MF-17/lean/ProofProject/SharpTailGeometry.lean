import ProofProject.OuterInteriorEstimate
import ProofProject.OuterPolynomialBoundary
import ProofProject.PolynomialGeometryReduction

/-!
# The sharp Hilbert tail geometry estimate

The finite projection hypothesis gives the actual rational phase approximation,
analytic sector and radial estimate, hence the scalar outer-polynomial bound.
The previously proved Gram factorization transfers it to every Hilbert space.
-/

noncomputable section

namespace ProofProject

open MeasureTheory

universe u

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

theorem sharp_outerPolynomial_estimate :
    HasSharpOuterPolynomialEstimate (16 * Real.exp 2) := by
  refine ⟨by positivity, ?_⟩
  intro K hK n hn p hdeg hp hproj
  apply outerPolynomial_boundary_bound p hK hn hdeg
    (integral_nonneg fun _ => sq_nonneg _)
  intro z hz
  exact outerPolynomial_interior_estimate hp hproj hK hz

/-- One absolute constant works for every bound K>1, dimension, family,
and complex Hilbert space in the fixed arbitrary universe. -/
theorem sharp_tail_geometry : HasSharpTailGeometry.{u} (16 * Real.exp 2) :=
  hasSharpTailGeometry_of_outerPolynomial sharp_outerPolynomial_estimate

end ProofProject
