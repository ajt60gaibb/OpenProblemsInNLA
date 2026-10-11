import NLA.Proofs.SP14.BaseExteriorSeries
import NLA.Proofs.SP14.BaseFourierMode
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Termwise integration of the normalized exterior base series under the exact
real-interval Fourier integral in the frozen SP-14 statement.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral Set

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private noncomputable def baseFourierPhase (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))

private theorem baseFourierPhase_norm (k : ℤ) (t : ℝ) :
    ‖baseFourierPhase k t‖ = 1 := by
  have harg : -((k : ℂ) * Complex.I * (t : ℂ)) =
      (((-(k : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [baseFourierPhase, harg, Complex.norm_exp_ofReal_mul_I]

private noncomputable def baseFourierTerm (k : ℤ) (n : ℕ) : C(ℝ, ℂ) where
  toFun t := baseCoeff n *
    (Circle.exp t : ℂ) ^ (1 - 2 * (n : ℤ)) * baseFourierPhase k t
  continuous_toFun := by
    have hp : Continuous (fun t : ℝ => (Circle.exp t : Circle) ^
        (1 - 2 * (n : ℤ))) :=
      (continuous_zpow _).comp Circle.exp.continuous
    have hcoe : Continuous (fun t : ℝ => (Circle.exp t : ℂ) ^
        (1 - 2 * (n : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro t
      exact Circle.coe_zpow _ _
    have hphase : Continuous (baseFourierPhase k) := by
      unfold baseFourierPhase
      fun_prop
    exact (continuous_const.mul hcoe).mul hphase

private theorem baseFourierTerm_norm (k : ℤ) (n : ℕ) (t : ℝ) :
    ‖baseFourierTerm k n t‖ = ‖baseCoeff n‖ := by
  simp only [baseFourierTerm, ContinuousMap.coe_mk, norm_mul, norm_zpow,
    Circle.norm_coe, one_zpow, baseFourierPhase_norm, mul_one]

/-- The frozen Fourier integral of the exterior series is the exact sum of
its integer-mode integrals; this includes every positive and negative mode. -/
theorem baseExteriorSymbol_fourier_tsum (k : ℤ) :
    FourierCoefficient baseExteriorSymbol k =
      ∑' n : ℕ,
        baseCoeff n * (if 1 - 2 * (n : ℤ) = k then 1 else 0) := by
  let F := baseFourierTerm k
  let K : TopologicalSpace.Compacts ℝ :=
    ⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩
  have hbound (n : ℕ) : ‖(F n).restrict K‖ ≤ ‖baseCoeff n‖ := by
    rw [ContinuousMap.norm_le ((F n).restrict K) (norm_nonneg _)]
    intro t
    exact le_of_eq (baseFourierTerm_norm k n t)
  have hsum : Summable (fun n : ℕ => ‖(F n).restrict K‖) := by
    apply Summable.of_norm_bounded summable_norm_baseCoeff
    intro n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound n
  have hintegral : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..(2 * Real.pi), F n t)
      (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
    exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (by simpa [K] using hsum)
  have hpoint (t : ℝ) : (∑' n : ℕ, F n t) =
      baseExteriorSymbol (Circle.exp t) * baseFourierPhase k t := by
    have hs := (summable_baseExterior_terms (Circle.exp t)).hasSum.mul_right
      (baseFourierPhase k t)
    simpa [F, baseFourierTerm, baseExteriorSymbol, mul_assoc] using hs.tsum_eq
  have hterm (n : ℕ) :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) =
          baseCoeff n * (if 1 - 2 * (n : ℤ) = k then 1 else 0) := by
    have hmode := FourierCoefficient_circle_mode (1 - 2 * (n : ℤ)) k
    unfold FourierCoefficient at hmode
    change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (baseCoeff n * (Circle.exp t : ℂ) ^ (1 - 2 * (n : ℤ))) *
          baseFourierPhase k t) = _
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (baseCoeff n * ∫ t in (0 : ℝ)..(2 * Real.pi),
            (Circle.exp t : ℂ) ^ (1 - 2 * (n : ℤ)) * baseFourierPhase k t) =
        baseCoeff n *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..(2 * Real.pi),
              (Circle.exp t : ℂ) ^ (1 - 2 * (n : ℤ)) * baseFourierPhase k t) := by ring
      _ = _ := by simpa [baseFourierPhase] using congrArg (baseCoeff n * ·) hmode
  calc
    FourierCoefficient baseExteriorSymbol k =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
      unfold FourierCoefficient
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simpa [baseFourierPhase] using (hpoint t).symm
    _ = ∑' n : ℕ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) :=
      (hintegral.mul_left _).tsum_eq.symm
    _ = ∑' n : ℕ,
          baseCoeff n * (if 1 - 2 * (n : ℤ) = k then 1 else 0) := by
      apply tsum_congr
      intro n
      exact hterm n

#assert_trust kernel baseExteriorSymbol_fourier_tsum
#print axioms baseExteriorSymbol_fourier_tsum

end NLA.Proofs.SP14
