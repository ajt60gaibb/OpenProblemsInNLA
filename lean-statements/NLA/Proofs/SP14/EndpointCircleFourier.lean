import NLA.Proofs.SP14.EndpointCircleSeries
import NLA.Proofs.SP14.BaseFourierMode
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The frozen real-interval Fourier coefficients of the continuous endpoint
circle series. Both signs and the zero mode use the original SP-14 integral.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral Set

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

private noncomputable def endpointCirclePhase (p : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))

private theorem endpointCirclePhase_norm (p : ℤ) (t : ℝ) :
    ‖endpointCirclePhase p t‖ = 1 := by
  have harg : -((p : ℂ) * Complex.I * (t : ℂ)) =
      (((-(p : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [endpointCirclePhase, harg, Complex.norm_exp_ofReal_mul_I]

private noncomputable def endpointCircleFourierTerm
    (c : ℕ → ℂ) (q : ℕ → ℤ) (p : ℤ) (n : ℕ) : C(ℝ, ℂ) where
  toFun t := c n * (Circle.exp t : ℂ) ^ (q n) * endpointCirclePhase p t
  continuous_toFun := by
    have hp : Continuous (fun t : ℝ => (Circle.exp t : Circle) ^ (q n)) :=
      (continuous_zpow _).comp Circle.exp.continuous
    have hcoe : Continuous (fun t : ℝ => (Circle.exp t : ℂ) ^ (q n)) := by
      apply (continuous_subtype_val.comp hp).congr
      intro t
      exact Circle.coe_zpow _ _
    have hphase : Continuous (endpointCirclePhase p) := by
      unfold endpointCirclePhase
      fun_prop
    exact (continuous_const.mul hcoe).mul hphase

private theorem endpointCircleFourierTerm_norm
    (c : ℕ → ℂ) (q : ℕ → ℤ) (p : ℤ) (n : ℕ) (t : ℝ) :
    ‖endpointCircleFourierTerm c q p n t‖ = ‖c n‖ := by
  simp only [endpointCircleFourierTerm, ContinuousMap.coe_mk, norm_mul, norm_zpow,
    Circle.norm_coe, one_zpow, endpointCirclePhase_norm, mul_one]

/-- Termwise integration of any absolutely summable integer-mode circle
series under the original normalized interval-integral Fourier definition. -/
private theorem endpointCircleFourier_tsum
    (c : ℕ → ℂ) (q : ℕ → ℤ)
    (hc : Summable (fun n : ℕ => ‖c n‖)) (p : ℤ) :
    FourierCoefficient (fun z : Circle => ∑' n : ℕ, c n * (z : ℂ) ^ (q n)) p =
      ∑' n : ℕ, c n * (if q n = p then 1 else 0) := by
  let F := endpointCircleFourierTerm c q p
  let K : TopologicalSpace.Compacts ℝ :=
    ⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩
  have hbound (n : ℕ) : ‖(F n).restrict K‖ ≤ ‖c n‖ := by
    rw [ContinuousMap.norm_le ((F n).restrict K) (norm_nonneg _)]
    intro t
    exact le_of_eq (endpointCircleFourierTerm_norm c q p n t)
  have hsum : Summable (fun n : ℕ => ‖(F n).restrict K‖) := by
    apply Summable.of_norm_bounded hc
    intro n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound n
  have hintegral : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..(2 * Real.pi), F n t)
      (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
    exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (by simpa [K] using hsum)
  have hpoint (t : ℝ) : (∑' n : ℕ, F n t) =
      (∑' n : ℕ, c n * (Circle.exp t : ℂ) ^ (q n)) *
        endpointCirclePhase p t := by
    have hterms : Summable (fun n : ℕ =>
        c n * (Circle.exp t : ℂ) ^ (q n)) := by
      apply Summable.of_norm_bounded hc
      intro n
      simp [norm_zpow]
    have hs := hterms.hasSum.mul_right (endpointCirclePhase p t)
    simpa [F, endpointCircleFourierTerm, mul_assoc] using hs.tsum_eq
  have hterm (n : ℕ) :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) =
          c n * (if q n = p then 1 else 0) := by
    have hmode := FourierCoefficient_circle_mode (q n) p
    unfold FourierCoefficient at hmode
    change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (c n * (Circle.exp t : ℂ) ^ (q n)) * endpointCirclePhase p t) = _
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (c n * ∫ t in (0 : ℝ)..(2 * Real.pi),
            (Circle.exp t : ℂ) ^ (q n) * endpointCirclePhase p t) =
        c n *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..(2 * Real.pi),
              (Circle.exp t : ℂ) ^ (q n) * endpointCirclePhase p t) := by ring
      _ = _ := by
        simpa [endpointCirclePhase] using congrArg (c n * ·) hmode
  calc
    FourierCoefficient (fun z : Circle => ∑' n : ℕ, c n * (z : ℂ) ^ (q n)) p =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
      unfold FourierCoefficient
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simpa [endpointCirclePhase] using (hpoint t).symm
    _ = ∑' n : ℕ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) :=
      (hintegral.mul_left _).tsum_eq.symm
    _ = ∑' n : ℕ, c n * (if q n = p then 1 else 0) := by
      apply tsum_congr
      intro n
      exact hterm n

private theorem FourierCoefficient_add_continuous
    (f g : Circle → ℂ) (hf : Continuous f) (hg : Continuous g) (p : ℤ) :
    FourierCoefficient (fun z => f z + g z) p =
      FourierCoefficient f p + FourierCoefficient g p := by
  have hcf : Continuous (fun t : ℝ =>
      f (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcg : Continuous (fun t : ℝ =>
      g (Circle.exp t) * Complex.exp (-((p : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hcf.intervalIntegrable 0 (2 * Real.pi))
    (hcg.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem endpointCirclePositive_fourier (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (p : ℤ) :
    FourierCoefficient (endpointCirclePositiveSeries r y) p =
      ∑' n : ℕ, physicalCoeff r y n * (if (n : ℤ) = p then 1 else 0) := by
  exact endpointCircleFourier_tsum (physicalCoeff r y) (fun n => (n : ℤ))
    (summable_endpointCirclePhysicalCoeff_norm r hrHalf y) p

private theorem endpointCircleNegative_fourier (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) (p : ℤ) :
    FourierCoefficient (endpointCircleNegativeSeries r v) p =
      ∑' n : ℕ, physicalCoeff r v n *
        (if -((n + 1 : ℕ) : ℤ) = p then 1 else 0) := by
  exact endpointCircleFourier_tsum (physicalCoeff r v)
    (fun n => -((n + 1 : ℕ) : ℤ))
    (summable_endpointCirclePhysicalCoeff_norm r hrHalf v) p

private theorem endpointCirclePositive_fourier_nonneg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (k : ℕ) :
    FourierCoefficient (endpointCirclePositiveSeries r y) (k : ℤ) =
      physicalCoeff r y k := by
  rw [endpointCirclePositive_fourier r hrHalf y]
  rw [tsum_eq_single k]
  · simp
  · intro n hn
    have hne : (n : ℤ) ≠ (k : ℤ) := by
      intro h
      exact hn (by exact_mod_cast h)
    simp [hne]

private theorem endpointCirclePositive_fourier_neg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (t : ℕ) :
    FourierCoefficient (endpointCirclePositiveSeries r y)
      (-((t + 1 : ℕ) : ℤ)) = 0 := by
  rw [endpointCirclePositive_fourier r hrHalf y]
  have hzero (n : ℕ) :
      physicalCoeff r y n *
        (if (n : ℤ) = -((t + 1 : ℕ) : ℤ) then 1 else 0) = 0 := by
    split_ifs with h
    · omega
    · simp
  simp_rw [hzero]
  simp

private theorem endpointCircleNegative_fourier_nonneg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) (k : ℕ) :
    FourierCoefficient (endpointCircleNegativeSeries r v) (k : ℤ) = 0 := by
  rw [endpointCircleNegative_fourier r hrHalf v]
  have hzero (n : ℕ) :
      physicalCoeff r v n *
        (if -((n + 1 : ℕ) : ℤ) = (k : ℤ) then 1 else 0) = 0 := by
    split_ifs with h
    · omega
    · simp
  simp_rw [hzero]
  simp

private theorem endpointCircleNegative_fourier_neg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (v : SobolevCoeff r) (t : ℕ) :
    FourierCoefficient (endpointCircleNegativeSeries r v)
      (-((t + 1 : ℕ) : ℤ)) = physicalCoeff r v t := by
  rw [endpointCircleNegative_fourier r hrHalf v]
  rw [tsum_eq_single t]
  · simp
  · intro n hn
    have hne : -((n + 1 : ℕ) : ℤ) ≠ -((t + 1 : ℕ) : ℤ) := by
      intro h
      have : n = t := by omega
      exact hn this
    split_ifs with h
    · omega
    · simp

/-- The frozen nonnegative Fourier coefficients of the actual circle
realization are exactly the input's physical coefficients. -/
theorem endpointCircleRealization_fourier_nonneg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (k : ℕ) :
    FourierCoefficient (endpointCircleRealization r hrHalf hr1 y) (k : ℤ) =
      physicalCoeff r y k := by
  let v := endpointNegativeOperator r (by linarith : 0 < r) hr1 y
  change FourierCoefficient
    (fun z => endpointCirclePositiveSeries r y z + endpointCircleNegativeSeries r v z)
    (k : ℤ) = physicalCoeff r y k
  rw [FourierCoefficient_add_continuous
    (endpointCirclePositiveSeries r y) (endpointCircleNegativeSeries r v)
    (continuous_endpointCirclePositiveSeries r hrHalf y)
    (continuous_endpointCircleNegativeSeries r hrHalf v) (k : ℤ)]
  rw [endpointCirclePositive_fourier_nonneg r hrHalf y k,
    endpointCircleNegative_fourier_nonneg r hrHalf v k]
  simp

/-- The frozen mode `-(t+1)` coefficient is exactly the actual negative
Fourier operator output in physical coordinates. -/
theorem endpointCircleRealization_fourier_neg (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (hr1 : r < 1)
    (y : SobolevCoeff r) (t : ℕ) :
    FourierCoefficient (endpointCircleRealization r hrHalf hr1 y)
      (-((t + 1 : ℕ) : ℤ)) =
        physicalCoeff r (endpointNegativeOperator r (by linarith) hr1 y) t := by
  let v := endpointNegativeOperator r (by linarith : 0 < r) hr1 y
  change FourierCoefficient
    (fun z => endpointCirclePositiveSeries r y z + endpointCircleNegativeSeries r v z)
    (-((t + 1 : ℕ) : ℤ)) = physicalCoeff r v t
  rw [FourierCoefficient_add_continuous
    (endpointCirclePositiveSeries r y) (endpointCircleNegativeSeries r v)
    (continuous_endpointCirclePositiveSeries r hrHalf y)
    (continuous_endpointCircleNegativeSeries r hrHalf v) (-((t + 1 : ℕ) : ℤ))]
  rw [endpointCirclePositive_fourier_neg r hrHalf y t,
    endpointCircleNegative_fourier_neg r hrHalf v t]
  simp

#assert_trust kernel endpointCircleRealization_fourier_nonneg
#assert_trust kernel endpointCircleRealization_fourier_neg
#print axioms endpointCircleRealization_fourier_neg

end NLA.Proofs.SP14
