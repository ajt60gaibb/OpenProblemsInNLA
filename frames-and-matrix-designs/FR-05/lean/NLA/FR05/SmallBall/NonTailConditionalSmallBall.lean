/-
The non-tail conditional small-ball branch of source Lemma 3.6.

The source splits on the deterministic scalar phase term
`sigma / 2 + beta cos(phi) - gamma sin(phi)`.  Away from its small
sublevel set, a Gaussian interval estimate uniform in the variance controls
the tail perturbation. This module combines the scalar estimate from
`GaussianSmallBall` with the product-phase bound, before the outer radial mixture.
-/
import NLA.FR05.SmallBall.PhaseAbsolute
import NLA.FR05.SmallBall.TailConditionalSmallBall

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace NLA.FR05

/-- The literal source scalar term from equation (3.21), plus an independent
real Gaussian perturbation.  This is the non-tail conditional event before
the outer radial mixture is introduced. -/
def sourceScalarGaussianSmallBallEvent
    (σ β γ u : ℝ) : Set (ℝ × ℝ) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |sourceScalarPhase σ β γ x.1 + x.2| ≤ u}

theorem measurableSet_sourceScalarGaussianSmallBallEvent
    (σ β γ u : ℝ) :
    MeasurableSet (sourceScalarGaussianSmallBallEvent σ β γ u) := by
  unfold sourceScalarGaussianSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × ℝ => |sourceScalarPhase σ β γ x.1 + x.2|) ⁻¹' Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    unfold sourceScalarPhase
    fun_prop

/-- The source's second conditional branch, after splitting phase into the
small deterministic-scalar set and its complement.  The Gaussian interval
bound is uniform in its variance, so the result includes the degenerate
variance case.  The resulting two terms are exactly balanced by
`t = u^(2/3)` in the informal source proof. -/
theorem sourceUniformInterval_prod_sourceScalarGaussianSmallBall_le
    (σ β γ u t : ℝ) {v : ℝ≥0}
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (gaussianReal 0 v))
        (sourceScalarGaussianSmallBallEvent σ β γ u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let hgaussian : IsProbabilityMeasure (gaussianReal 0 v) := inferInstance
  apply @prod_measure_le_add_of_bad_sections ℝ ℝ _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (gaussianReal 0 v) hphase hgaussian
    (sourceScalarGaussianSmallBallEvent σ β γ u)
    (measurableSet_sourceScalarGaussianSmallBallEvent σ β γ u)
    (sourceScalarPhaseSublevel σ β γ t)
    (measurableSet_sourceScalarPhaseSublevel σ β γ t)
    (ENNReal.ofReal (2 * Real.sqrt (2 * t)))
    (ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)))
  · exact sourceUniformInterval_sourceScalarPhaseSublevel_le_two_sqrt_two_mul
      σ β γ t ht.le hcoeff
  · intro φ hφ
    by_cases hsupport : φ ∈ Icc 0 (2 * Real.pi)
    · have hnotle : ¬ |sourceScalarPhase σ β γ φ| ≤ t := by
        intro hle
        exact hφ ⟨hsupport, hle⟩
      have hcentre : t ≤ |sourceScalarPhase σ β γ φ| :=
        (lt_of_not_ge hnotle).le
      change gaussianReal 0 v
          {w : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
            |sourceScalarPhase σ β γ φ + w| ≤ u} ≤ _
      simp only [hsupport, true_and]
      exact gaussianReal_abs_add_smallBall_uniform
        (sourceScalarPhase σ β γ φ) u t ht hcentre hscale
    · have hempty :
        {w : ℝ | (φ, w) ∈ sourceScalarGaussianSmallBallEvent σ β γ u} = ∅ := by
          ext w
          change (φ ∈ Icc 0 (2 * Real.pi) ∧
            |sourceScalarPhase σ β γ φ + w| ≤ u) ↔ w ∈ (∅ : Set ℝ)
          simp only [hsupport, false_and]
          exact (Set.mem_empty_iff_false w).symm
      rw [hempty, measure_empty]
      exact bot_le

/-- The source choice `t = u^(2/3)` written without real-power machinery:
put `u = r^3` and `t = r^2`.  For `0 < r ≤ 1/2`, the non-tail conditional
probability is explicitly bounded by a fixed constant times `r`, i.e.
by `O(u^(1/3))`. -/
theorem sourceUniformInterval_prod_sourceScalarGaussianSmallBall_cubic_le
    (σ β γ r : ℝ) {v : ℝ≥0}
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (gaussianReal 0 v))
        (sourceScalarGaussianSmallBallEvent σ β γ (r ^ 3)) ≤
      ENNReal.ofReal (2 * Real.sqrt 2 * r) +
        ENNReal.ofReal (6 * r / Real.sqrt (2 * Real.pi)) := by
  have hscale : 2 * r ^ 3 ≤ r ^ 2 := by
    calc
      2 * r ^ 3 = (2 * r) * r ^ 2 := by ring
      _ ≤ 1 * r ^ 2 := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact sq_nonneg r
      _ = r ^ 2 := by ring
  have hmain := sourceUniformInterval_prod_sourceScalarGaussianSmallBall_le
    σ β γ (r ^ 3) (r ^ 2) (sq_pos_of_pos hr) hscale hcoeff (v := v)
  have hsqrt : Real.sqrt (2 * r ^ 2) = Real.sqrt 2 * r := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hr]
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 Real.two_pi_pos)
  have hratio :
      6 * r ^ 3 / (Real.sqrt (2 * Real.pi) * r ^ 2) =
        6 * r / Real.sqrt (2 * Real.pi) := by
    field_simp [hsqrtTwoPi, hr.ne']
  rw [hsqrt, hratio] at hmain
  simpa only [mul_assoc] using hmain

end NLA.FR05
