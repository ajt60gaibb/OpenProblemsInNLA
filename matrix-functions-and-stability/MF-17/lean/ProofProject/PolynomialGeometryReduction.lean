import ProofProject.OuterCircleWeight

/-!
# Reduction of sharp Hilbert geometry to a scalar outer polynomial estimate

The scalar analytic estimate is a proof-side interface. `SharpTailGeometry`
proves it with an absolute constant. The finite Hilbert-family construction
and its reduction to this scalar estimate include the all-zero family.
-/

noncomputable section

open MeasureTheory

namespace ProofProject

universe u

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def HasPolynomialCircleProjectionBound (p : Polynomial ℂ) (K : ℝ) : Prop :=
  ∀ c : ℤ →₀ ℂ,
    (∫ z : AddCircle (1 : ℝ),
      ‖laurentCirclePolynomial (c.filter (fun m => 0 ≤ m)) z‖ ^ 2 *
        ‖p.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle) ≤
      K ^ 2 * ∫ z : AddCircle (1 : ℝ),
        ‖laurentCirclePolynomial c z‖ ^ 2 * ‖p.eval (fourier 1 z)‖ ^ 2
          ∂AddCircle.haarAddCircle

/-- The scalar analytic interface for sharp geometry. Its constant precedes
the projection bound, dimension parameter, and polynomial. An unconditional
proof is given in `SharpTailGeometry`. -/
def HasSharpOuterPolynomialEstimate (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ {K : ℝ}, 1 < K → ∀ {n : ℕ}, 1 ≤ n →
    ∀ p : Polynomial ℂ, p.natDegree ≤ n - 1 →
      (∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) →
      HasPolynomialCircleProjectionBound p K →
      ‖p.eval 1‖ ^ 2 ≤ C * K ^ 2 * (n : ℝ) ^ growthExponent K *
        ∫ z : AddCircle (1 : ℝ), ‖p.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle

/-- The scalar estimate implies the exact Hilbert geometry statement
in every fixed universe, with the same absolute constant and exponent. -/
theorem hasSharpTailGeometry_of_outerPolynomial {C : ℝ}
    (hscalar : HasSharpOuterPolynomialEstimate C) : HasSharpTailGeometry.{u} C := by
  refine ⟨hscalar.1, ?_⟩
  intro K hK H hH hIH n v htail
  by_cases hv : ∃ j, v j ≠ 0
  · have hn : 1 ≤ n := by
      obtain ⟨j, _⟩ := hv
      have := j.isLt
      omega
    obtain ⟨p, hdeg, hnz, hw⟩ := exists_outerPolynomial_of_tail_bound htail hn hv
    have hproj : HasPolynomialCircleProjectionBound p K :=
      fun c => outerPolynomial_nonnegative_projection_le htail p hw c
    have hb := hscalar.2 hK hn p hdeg hnz hproj
    rw [outerPolynomial_value_one v p hw, outerPolynomial_circle_mean v p hw] at hb
    exact hb
  · have hall : ∀ j, v j = 0 := by simpa only [not_exists, not_not] using hv
    simp [finiteSynthesis, hall]

end ProofProject
