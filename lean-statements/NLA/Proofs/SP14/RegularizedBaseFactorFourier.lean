import NLA.Proofs.SP14.RegularizedBaseCoeff
import NLA.Proofs.SP14.BaseExteriorFactor
import NLA.Proofs.SP14.BaseFourierMode
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The actual endpoint-regularized exterior factor `(1+s)g₀(s)` has exactly
one positive Fourier mode and the reviewed regularized negative modes.
The frozen real-interval Fourier normalization is used throughout.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory intervalIntegral Set

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

noncomputable def regularizedBaseFactor (s : Circle) : ℂ :=
  (1 + (s : ℂ)) * baseExteriorFactor s

theorem continuous_regularizedBaseFactor : Continuous regularizedBaseFactor := by
  unfold regularizedBaseFactor
  exact (continuous_const.add continuous_subtype_val).mul continuous_baseExteriorFactor

private theorem summable_norm_regularizedBaseCoeff :
    Summable (fun n : ℕ => ‖regularizedBaseCoeff n‖) := by
  have hshift : Summable (fun n : ℕ => ‖baseCoeff (n + 1)‖) :=
    (summable_nat_add_iff 1).mpr summable_norm_baseCoeff
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (fun n => by
      simpa [regularizedBaseCoeff] using
        norm_add_le (baseCoeff n) (baseCoeff (n + 1)))
    (summable_norm_baseCoeff.add hshift)

private theorem summable_regularizedBase_terms (s : Circle) :
    Summable (fun n : ℕ => regularizedBaseCoeff n * (s : ℂ) ^ (-(n : ℤ))) := by
  apply Summable.of_norm_bounded summable_norm_regularizedBaseCoeff
  intro n
  rw [norm_mul, norm_zpow, Circle.norm_coe, one_zpow, mul_one]

theorem regularizedBaseFactor_series (s : Circle) :
    regularizedBaseFactor s =
      (s : ℂ) + ∑' n : ℕ,
        regularizedBaseCoeff n * (s : ℂ) ^ (-(n : ℤ)) := by
  let f : ℕ → ℂ := fun n => baseCoeff n * (s : ℂ) ^ (-(n : ℤ))
  let g : ℕ → ℂ := fun n => baseCoeff (n + 1) * (s : ℂ) ^ (-(n : ℤ))
  have hs : (s : ℂ) ≠ 0 := Circle.coe_ne_zero s
  have hf : Summable f := summable_baseExteriorFactor_terms s
  have hg : Summable g := by
    apply Summable.of_norm_bounded
      ((summable_nat_add_iff 1).mpr summable_norm_baseCoeff)
    intro n
    simp [g, Circle.norm_coe]
  have hshift (n : ℕ) : (s : ℂ) * f (n + 1) = g n := by
    dsimp [f, g]
    have he : (1 : ℤ) + -((n + 1 : ℕ) : ℤ) = -(n : ℤ) := by omega
    calc
      (s : ℂ) * (baseCoeff (n + 1) * (s : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) =
          baseCoeff (n + 1) * ((s : ℂ) ^ (1 : ℤ) *
            (s : ℂ) ^ (-((n + 1 : ℕ) : ℤ))) := by simp; ring
      _ = baseCoeff (n + 1) * (s : ℂ) ^ (-(n : ℤ)) := by
        rw [← zpow_add₀ hs, he]
  have hmul : (s : ℂ) * (∑' n : ℕ, f n) =
      (s : ℂ) + ∑' n : ℕ, g n := by
    have hsplit := hf.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one] at hsplit
    rw [← hsplit]
    have hf0 : f 0 = 1 := by simp [f, baseCoeff]
    rw [hf0, mul_add, mul_one]
    rw [← tsum_mul_left]
    congr 1
    apply tsum_congr
    exact hshift
  calc
    regularizedBaseFactor s =
        (∑' n : ℕ, f n) + (s : ℂ) * (∑' n : ℕ, f n) := by
      simp [regularizedBaseFactor, baseExteriorFactor, f, add_mul]
    _ = (s : ℂ) + ((∑' n : ℕ, f n) + (∑' n : ℕ, g n)) := by
      rw [hmul]
      abel
    _ = (s : ℂ) + ∑' n : ℕ,
          regularizedBaseCoeff n * (s : ℂ) ^ (-(n : ℤ)) := by
      rw [← hf.tsum_add hg]
      congr 1
      apply tsum_congr
      intro n
      simp [f, g, regularizedBaseCoeff, add_mul]

private noncomputable def regularizedFourierPhase (k : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))

private theorem regularizedFourierPhase_norm (k : ℤ) (t : ℝ) :
    ‖regularizedFourierPhase k t‖ = 1 := by
  have harg : -((k : ℂ) * Complex.I * (t : ℂ)) =
      (((-(k : ℝ) * t) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [regularizedFourierPhase, harg, Complex.norm_exp_ofReal_mul_I]

private noncomputable def regularizedFourierTerm (k : ℤ) (n : ℕ) : C(ℝ, ℂ) where
  toFun t := regularizedBaseCoeff n *
    (Circle.exp t : ℂ) ^ (-(n : ℤ)) * regularizedFourierPhase k t
  continuous_toFun := by
    have hp : Continuous (fun t : ℝ => (Circle.exp t : Circle) ^ (-(n : ℤ))) :=
      (continuous_zpow _).comp Circle.exp.continuous
    have hcoe : Continuous (fun t : ℝ => (Circle.exp t : ℂ) ^ (-(n : ℤ))) := by
      apply (continuous_subtype_val.comp hp).congr
      intro t
      exact Circle.coe_zpow _ _
    have hphase : Continuous (regularizedFourierPhase k) := by
      unfold regularizedFourierPhase
      fun_prop
    exact (continuous_const.mul hcoe).mul hphase

private theorem regularizedFourierTerm_norm (k : ℤ) (n : ℕ) (t : ℝ) :
    ‖regularizedFourierTerm k n t‖ = ‖regularizedBaseCoeff n‖ := by
  simp only [regularizedFourierTerm, ContinuousMap.coe_mk, norm_mul, norm_zpow,
    Circle.norm_coe, one_zpow, regularizedFourierPhase_norm, mul_one]

private noncomputable def regularizedBaseTail (s : Circle) : ℂ :=
  ∑' n : ℕ, regularizedBaseCoeff n * (s : ℂ) ^ (-(n : ℤ))

private theorem continuous_regularizedBaseTail : Continuous regularizedBaseTail := by
  have heq : regularizedBaseTail = fun s : Circle => regularizedBaseFactor s - (s : ℂ) := by
    funext s
    simp only [regularizedBaseTail]
    rw [regularizedBaseFactor_series]
    ring
  rw [heq]
  exact continuous_regularizedBaseFactor.sub continuous_subtype_val

private theorem regularizedBaseTail_fourier_tsum (k : ℤ) :
    FourierCoefficient regularizedBaseTail k =
      ∑' n : ℕ, regularizedBaseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
  let F := regularizedFourierTerm k
  let K : TopologicalSpace.Compacts ℝ :=
    ⟨uIcc (0 : ℝ) (2 * Real.pi), isCompact_uIcc⟩
  have hbound (n : ℕ) : ‖(F n).restrict K‖ ≤ ‖regularizedBaseCoeff n‖ := by
    rw [ContinuousMap.norm_le ((F n).restrict K) (norm_nonneg _)]
    intro t
    exact le_of_eq (regularizedFourierTerm_norm k n t)
  have hsum : Summable (fun n : ℕ => ‖(F n).restrict K‖) := by
    apply Summable.of_norm_bounded summable_norm_regularizedBaseCoeff
    intro n
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hbound n
  have hintegral : HasSum (fun n : ℕ => ∫ t in (0 : ℝ)..(2 * Real.pi), F n t)
      (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
    exact intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (by simpa [K] using hsum)
  have hpoint (t : ℝ) : (∑' n : ℕ, F n t) =
      regularizedBaseTail (Circle.exp t) * regularizedFourierPhase k t := by
    have hs := (summable_regularizedBase_terms (Circle.exp t)).hasSum.mul_right
      (regularizedFourierPhase k t)
    simpa [F, regularizedFourierTerm, regularizedBaseTail, mul_assoc] using hs.tsum_eq
  have hterm (n : ℕ) :
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) =
          regularizedBaseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
    have hmode := FourierCoefficient_circle_mode (-(n : ℤ)) k
    unfold FourierCoefficient at hmode
    change (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        (regularizedBaseCoeff n * (Circle.exp t : ℂ) ^ (-(n : ℤ))) *
          regularizedFourierPhase k t) = _
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul]
    calc
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (regularizedBaseCoeff n * ∫ t in (0 : ℝ)..(2 * Real.pi),
            (Circle.exp t : ℂ) ^ (-(n : ℤ)) * regularizedFourierPhase k t) =
        regularizedBaseCoeff n *
          (((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (0 : ℝ)..(2 * Real.pi),
              (Circle.exp t : ℂ) ^ (-(n : ℤ)) * regularizedFourierPhase k t) := by ring
      _ = _ := by
        simpa [regularizedFourierPhase] using
          congrArg (regularizedBaseCoeff n * ·) hmode
  calc
    FourierCoefficient regularizedBaseTail k =
        (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ t in (0 : ℝ)..(2 * Real.pi), ∑' n : ℕ, F n t) := by
      unfold FourierCoefficient
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      simpa [regularizedFourierPhase] using (hpoint t).symm
    _ = ∑' n : ℕ,
          (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
            (∫ t in (0 : ℝ)..(2 * Real.pi), F n t) :=
      (hintegral.mul_left _).tsum_eq.symm
    _ = ∑' n : ℕ,
          regularizedBaseCoeff n * (if -(n : ℤ) = k then 1 else 0) := by
      apply tsum_congr
      intro n
      exact hterm n

private theorem FourierCoefficient_add_of_continuous
    (a b : Circle → ℂ) (ha : Continuous a) (hb : Continuous b) (k : ℤ) :
    FourierCoefficient (fun z => a z + b z) k =
      FourierCoefficient a k + FourierCoefficient b k := by
  have hca : Continuous (fun t : ℝ =>
      a (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  have hcb : Continuous (fun t : ℝ =>
      b (Circle.exp t) * Complex.exp (-((k : ℂ) * Complex.I * (t : ℂ)))) := by
    fun_prop
  unfold FourierCoefficient
  simp_rw [add_mul]
  rw [intervalIntegral.integral_add
    (hca.intervalIntegrable 0 (2 * Real.pi))
    (hcb.intervalIntegrable 0 (2 * Real.pi))]
  ring

private theorem regularizedBaseTail_fourier_value (k : ℤ) :
    FourierCoefficient regularizedBaseTail k =
      if k ≤ 0 then regularizedBaseCoeff k.natAbs else 0 := by
  rw [regularizedBaseTail_fourier_tsum]
  by_cases hk : k ≤ 0
  · have hn : -((k.natAbs : ℕ) : ℤ) = k := by omega
    have hsingle (n : ℕ) (hne : n ≠ k.natAbs) :
        regularizedBaseCoeff n * (if -(n : ℤ) = k then 1 else 0) = 0 := by
      have hmode : -(n : ℤ) ≠ k := by
        intro heq
        have : n = k.natAbs := by omega
        exact hne this
      simp [hmode]
    rw [tsum_eq_single k.natAbs hsingle]
    rw [if_pos hn]
    simp [hk]
  · have hzero (n : ℕ) :
        regularizedBaseCoeff n * (if -(n : ℤ) = k then 1 else 0) = 0 := by
      have hmode : -(n : ℤ) ≠ k := by omega
      simp [hmode]
    simp_rw [hzero]
    simp [hk]

/-- The actual regularized factor has one positive mode and precisely the
regularized exterior coefficients at every nonpositive integer mode. -/
theorem regularizedBaseFactor_fourier (k : ℤ) :
    FourierCoefficient regularizedBaseFactor k =
      if k = 1 then 1
      else if k ≤ 0 then regularizedBaseCoeff k.natAbs
      else 0 := by
  have hfun : regularizedBaseFactor =
      fun s : Circle => (s : ℂ) + regularizedBaseTail s := by
    funext s
    exact regularizedBaseFactor_series s
  rw [hfun, FourierCoefficient_add_of_continuous
    (fun s : Circle => (s : ℂ)) regularizedBaseTail
    continuous_subtype_val continuous_regularizedBaseTail k]
  have hmode : FourierCoefficient (fun s : Circle => (s : ℂ)) k =
      if (1 : ℤ) = k then 1 else 0 := by
    simpa using FourierCoefficient_circle_mode 1 k
  rw [hmode, regularizedBaseTail_fourier_value]
  by_cases hk1 : k = 1
  · subst k
    simp
  · by_cases hk0 : k ≤ 0
    · have hk1' : (1 : ℤ) ≠ k := Ne.symm hk1
      simp [hk1, hk1', hk0]
    · have hk1' : (1 : ℤ) ≠ k := Ne.symm hk1
      simp [hk1, hk1', hk0]

#assert_trust kernel continuous_regularizedBaseFactor
#assert_trust kernel regularizedBaseFactor_series
#assert_trust kernel regularizedBaseFactor_fourier

end NLA.Proofs.SP14
