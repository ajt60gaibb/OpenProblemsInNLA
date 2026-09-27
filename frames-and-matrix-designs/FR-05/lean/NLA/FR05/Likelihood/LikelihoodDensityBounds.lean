import NLA.FR05.Likelihood.UniformKernels
import NLA.FR05.Overlap.HaarOverlapDensity

/-!
# Likelihood density bounds on the local and tail regions

The sections develop `LikelihoodLocalBounds`, `LikelihoodDensityBounds`, `LikelihoodTailBounds`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section LikelihoodLocalBounds

open Filter
open scoped Topology

def sourceTaylorConstant : ℝ := 11000 * kernelMomentConstant 4

theorem sourceTaylorConstant_pos : 0 < sourceTaylorConstant := by
  unfold sourceTaylorConstant kernelMomentConstant
  positivity

def sourceLocalRadius : ℝ := min (1 / 128) (1 / (1600 * (sourceTaylorConstant + 1)))

theorem sourceLocalRadius_pos : 0 < sourceLocalRadius := by
  unfold sourceLocalRadius
  exact lt_min (by norm_num) (by have := sourceTaylorConstant_pos; positivity)

theorem sourceLocalRadius_le : sourceLocalRadius ≤ 1 / 128 :=
  min_le_left _ _

theorem source_local_remainder_small {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ sourceLocalRadius) :
    sourceTaylorConstant * overlapFrobeniusSq K ≤ 1 / 800 := by
  have hr := sourceLocalRadius_pos
  have hr1 := sourceLocalRadius_le
  have hR := sourceTaylorConstant_pos
  have hF := overlapFrobeniusSq_le K
  have hρ := overlapOperatorNorm_nonneg K
  have hb := (le_div_iff₀ (show 0 < 1600 * (sourceTaylorConstant + 1) by positivity)).mp
    (min_le_right (1 / 128 : ℝ) (1 / (1600 * (sourceTaylorConstant + 1))))
  change sourceLocalRadius * (1600 * (sourceTaylorConstant + 1)) ≤ 1 at hb
  have hsq : overlapOperatorNorm K ^ 2 ≤ sourceLocalRadius := by
    nlinarith [sq_nonneg sourceLocalRadius]
  have hm := mul_le_mul_of_nonneg_left (show overlapFrobeniusSq K ≤ 2 * sourceLocalRadius by linarith) hR.le
  nlinarith

theorem source_local_kernel_exp {M : ℕ} (hM : 2 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ sourceLocalRadius) :
    sourceOverlapKernel hM a b K ≤ Real.exp ((199 / 800) * overlapFrobeniusSq K) := by
  by_cases hr : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2)
  · have he := sourceOverlapKernel_local_expansion hM a b hr (hK.trans sourceLocalRadius_le)
    have hq := source_covariance_gap hM
    have hs := source_local_remainder_small hK
    have hx := overlapFrobeniusSq_nonneg K
    have hqx := mul_le_mul_of_nonneg_right hq hx
    have hsx := mul_le_mul_of_nonneg_right hs hx
    norm_num [sourceEta] at hqx
    change |sourceOverlapKernel hM a b K - _| ≤ sourceTaylorConstant * _ at he
    apply le_trans _ (Real.add_one_le_exp _)
    have := (abs_le.mp he).2
    nlinarith
  · rw [sourceOverlapKernel_eq_zero hM a b K hr]
    exact (Real.exp_pos _).le

theorem source_local_power_density {M : ℕ} (hM : 1600 ≤ M)
    {a : ℝ} (ha : 0 ≤ a) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ sourceLocalRadius)
    (haexp : a ≤ Real.exp ((199 / 800) * overlapFrobeniusSq K))
    {n : ℕ} (hn : n ≤ 4 * M) :
    a ^ n * overlapDeterminant K ^ (M - 4) ≤
      Real.exp (-(1 / 400) * M * overlapFrobeniusSq K) := by
  have hball : overlapOperatorNorm K < 1 := lt_of_le_of_lt (hK.trans sourceLocalRadius_le) (by norm_num)
  have hx := overlapFrobeniusSq_nonneg K
  have hΔ := (overlapDeterminant_pos hball).le
  have hF : overlapFrobeniusSq K ≤ 2 := by
    have := overlapFrobeniusSq_le K
    have := overlapOperatorNorm_nonneg K
    nlinarith [sourceLocalRadius_le]
  have hdet := overlapDeterminant_le_exp K hF
  calc
    _ ≤ (Real.exp ((199 / 800) * overlapFrobeniusSq K)) ^ n *
        (Real.exp (-overlapFrobeniusSq K)) ^ (M - 4) := by gcongr
    _ = Real.exp ((n : ℝ) * ((199 / 800) * overlapFrobeniusSq K) +
        ((M - 4 : ℕ) : ℝ) * (-overlapFrobeniusSq K)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hn' : (n : ℝ) ≤ 4 * M := by exact_mod_cast hn
      have hm : (1600 : ℝ) ≤ M := by exact_mod_cast hM
      have hsub : ((M - 4 : ℕ) : ℝ) = (M : ℝ) - 4 := by rw [Nat.cast_sub (by lia)]; norm_num
      rw [hsub]
      have hh := mul_le_mul_of_nonneg_right hn' (mul_nonneg (by norm_num : (0 : ℝ) ≤ 199 / 800) hx)
      have hh' := mul_nonneg (show 0 ≤ (M : ℝ) / 400 - 4 by linarith) hx
      nlinarith

theorem tendsto_sourceEpsilon : Tendsto sourceEpsilon atTop (𝓝 0) := by
  exact ((tendsto_pow_atTop (α := ℝ) (by norm_num : 50 ≠ 0)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop

theorem source_tail_parameters_small :
    ∃ D : ℕ, ∀ M : ℕ, D ≤ M →
      2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 ≤ sourceLocalRadius ^ 2 / 4000 := by
  have h : Tendsto (fun M ↦ 2 * sourceDelta M + 2 * sourceEpsilon M ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_sourceDelta.const_mul 2).add ((tendsto_sourceEpsilon.pow 2).const_mul 2)
  have hp : 0 < sourceLocalRadius ^ 2 / 4000 := by have := sourceLocalRadius_pos; positivity
  obtain ⟨D, hD⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hp))
  exact ⟨D, fun M hM ↦ (hD M hM).le⟩

end LikelihoodLocalBounds

section LikelihoodDensityBounds

open MeasureTheory

def sourceOverlapPrefactor (M : ℕ) : ℝ :=
  (((M : ℝ) - 1) * ((M : ℝ) - 2) ^ 2 * ((M : ℝ) - 3)) / Real.pi ^ 4

theorem sourceOverlapPrefactor_nonneg {M : ℕ} (hM : 4 ≤ M) :
    0 ≤ sourceOverlapPrefactor M := by
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sourceOverlapPrefactor
  exact div_nonneg (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)) (by positivity)

theorem sourceOverlapPrefactor_le {M : ℕ} (hM : 4 ≤ M) :
    sourceOverlapPrefactor M ≤ (M : ℝ) ^ 4 := by
  have hm : (4 : ℝ) ≤ M := by exact_mod_cast hM
  have hpi : (1 : ℝ) ≤ Real.pi ^ 4 := by
    have := Real.two_le_pi
    nlinarith [sq_nonneg (Real.pi ^ 2 - 1)]
  unfold sourceOverlapPrefactor
  calc
    _ ≤ ((M : ℝ) - 1) * ((M : ℝ) - 2) ^ 2 * ((M : ℝ) - 3) :=
      div_le_self (mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (by linarith)) hpi
    _ ≤ (M : ℝ) * M ^ 2 * M := by gcongr <;> linarith
    _ = _ := by ring

theorem sourceOverlapLebesgueDensity_nonneg {M : ℕ} (hM : 4 ≤ M) (K : SourceOverlapMatrix) :
    0 ≤ sourceOverlapLebesgueDensity M K := by
  unfold sourceOverlapLebesgueDensity
  split_ifs with hK
  · exact mul_nonneg (sourceOverlapPrefactor_nonneg hM) (pow_nonneg (overlapDeterminant_pos hK).le _)
  · exact le_refl 0

@[fun_prop]
theorem measurable_sourceOverlapLebesgueDensity (M : ℕ) :
    Measurable (sourceOverlapLebesgueDensity M) := by
  unfold sourceOverlapLebesgueDensity
  exact Measurable.ite measurableSet_overlapOperatorNorm_lt_one (by fun_prop) measurable_const

theorem integral_sourceOverlapLaw_density {M : ℕ} (hM : 4 ≤ M) (f : SourceOverlapMatrix → ℝ) :
    (∫ K, f K ∂sourceOverlapLaw M (by lia)) =
      ∫ K, sourceOverlapLebesgueDensity M K * f K := by
  rw [lemma_3_5 hM, integral_withDensity_eq_integral_toReal_smul
    (measurable_sourceOverlapLebesgueDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (sourceOverlapLebesgueDensity_nonneg hM _), smul_eq_mul]

def sourceKernelDifference {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind)
    (K : SourceOverlapMatrix) : ℝ :=
  |sourceOverlapKernel hM a b K ^ sourceRowCount M -
    sourceOverlapKernel hM .reference .reference K ^ sourceRowCount M|

@[fun_prop]
theorem measurable_sourceKernelDifference {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    Measurable (sourceKernelDifference hM a b) :=
  (((measurable_sourceOverlapKernel hM a b).pow_const _).sub
    ((measurable_sourceOverlapKernel hM .reference .reference).pow_const _)).abs

theorem integrable_sourceKernelDifference {M : ℕ} (hM : 2 ≤ M) (a b : SourceDensityKind) :
    Integrable (sourceKernelDifference hM a b) (sourceOverlapLaw M hM) :=
  ((integrable_sourceOverlapKernel_pow hM a b _).sub
    (integrable_sourceOverlapKernel_pow hM .reference .reference _)).abs

theorem integrable_sourceWeightedKernelDifference {M : ℕ} (hM : 4 ≤ M) (a b : SourceDensityKind) :
    Integrable (fun K ↦ sourceOverlapLebesgueDensity M K *
      sourceKernelDifference (by lia : 2 ≤ M) a b K) := by
  have hi := integrable_sourceKernelDifference (by lia : 2 ≤ M) a b
  rw [lemma_3_5 hM] at hi
  have h := (integrable_withDensity_iff_integrable_smul'
    (measurable_sourceOverlapLebesgueDensity M).ennreal_ofReal
    (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hi
  simpa only [ENNReal.toReal_ofReal (sourceOverlapLebesgueDensity_nonneg hM _), smul_eq_mul] using h

theorem source_local_weighted_difference {M : ℕ} (hM : 1600 ≤ M)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hK : overlapOperatorNorm K ≤ sourceLocalRadius) :
    sourceOverlapLebesgueDensity M K * sourceKernelDifference (M := M) (by lia) a b K ≤
      8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
        Real.exp (-(1 / 400) * M * overlapFrobeniusSq K) := by
  have hm : 2 ≤ M := by lia
  have hball : overlapOperatorNorm K < 1 :=
    lt_of_le_of_lt (hK.trans sourceLocalRadius_le) (by norm_num)
  have hΔ := (overlapDeterminant_pos hball).le
  have hR := sourceTaylorConstant_pos.le
  by_cases hr : K ∈ Set.range (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hm p.1 p.2)
  · let u := sourceOverlapKernel hm a b K
    let v := sourceOverlapKernel hm .reference .reference K
    have hu : 0 ≤ u := sourceOverlapKernel_nonneg hm a b K
    have hv : 0 ≤ v := sourceOverlapKernel_nonneg hm .reference .reference K
    have hdiff : sourceKernelDifference hm a b K ≤
        2 * sourceTaylorConstant * overlapFrobeniusSq K ^ 2 * sourceRowCount M *
          max u v ^ (sourceRowCount M - 1) :=
      kernel_power_difference_le hu hv
        (sourceOverlapKernel_local_expansion hm a b hr (hK.trans sourceLocalRadius_le))
        (sourceOverlapKernel_local_expansion hm .reference .reference hr (hK.trans sourceLocalRadius_le)) _
    have hmax := source_local_power_density hM (le_max_of_le_left hu) hK
      (max_le (source_local_kernel_exp hm a b hK)
        (source_local_kernel_exp hm .reference .reference hK))
      (show sourceRowCount M - 1 ≤ 4 * M by unfold sourceRowCount; lia)
    have hN : (sourceRowCount M : ℝ) ≤ 4 * M := by
      exact_mod_cast (show sourceRowCount M ≤ 4 * M by unfold sourceRowCount; lia)
    have hd : 0 ≤ sourceKernelDifference hm a b K := abs_nonneg _
    rw [sourceOverlapLebesgueDensity, if_pos hball]
    change sourceOverlapPrefactor M * overlapDeterminant K ^ (M - 4) * _ ≤ _
    calc
      _ ≤ (M : ℝ) ^ 4 * overlapDeterminant K ^ (M - 4) *
          (2 * sourceTaylorConstant * overlapFrobeniusSq K ^ 2 * sourceRowCount M *
            max u v ^ (sourceRowCount M - 1)) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_right (sourceOverlapPrefactor_le (M := M) (by lia)) (pow_nonneg hΔ _))
          hdiff hd (by positivity)
      _ = 2 * sourceTaylorConstant * overlapFrobeniusSq K ^ 2 * sourceRowCount M * (M : ℝ) ^ 4 *
          (max u v ^ (sourceRowCount M - 1) * overlapDeterminant K ^ (M - 4)) := by ring
      _ ≤ 2 * sourceTaylorConstant * overlapFrobeniusSq K ^ 2 * (4 * M) * (M : ℝ) ^ 4 *
          Real.exp (-(1 / 400) * M * overlapFrobeniusSq K) := by gcongr
      _ = _ := by ring
  · simp only [sourceKernelDifference, sourceOverlapKernel_eq_zero hm a b K hr,
      sourceOverlapKernel_eq_zero hm .reference .reference K hr, sub_self, abs_zero, mul_zero]
    positivity

end LikelihoodDensityBounds

section LikelihoodTailBounds

open MeasureTheory

def sourceTailRate : ℝ := sourceLocalRadius ^ 2 / 1000

theorem sourceTailRate_pos : 0 < sourceTailRate := by
  unfold sourceTailRate
  have := sourceLocalRadius_pos
  positivity

def sourceTailCoefficient : ℝ :=
  (Real.exp 1 + 4) ^ 15 * Real.exp (5 * sourceTailRate)

theorem sourceTailCoefficient_pos : 0 < sourceTailCoefficient := by
  unfold sourceTailCoefficient
  positivity

theorem source_tail_power_determinant {M : ℕ} (hM : 5 ≤ M)
    (hp : 2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 ≤ sourceLocalRadius ^ 2 / 4000)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hball : overlapOperatorNorm K < 1) (hK : sourceLocalRadius < overlapOperatorNorm K) :
    sourceOverlapKernel (by lia : 2 ≤ M) a b K ^ sourceRowCount M *
      overlapDeterminant K ^ (M - 4) ≤
        sourceTailCoefficient * (M : ℝ) ^ 780 * Real.exp (-sourceTailRate * M) := by
  have hm : 2 ≤ M := by lia
  have hx := overlapFrobeniusSq_nonneg K
  have hF : overlapFrobeniusSq K ≤ 2 := (overlapOperatorNorm_lt_one_iff K).mp hball |>.1.le
  have hΔ := overlapDeterminant_pos hball
  have hΔ1 : overlapDeterminant K ≤ 1 :=
    (overlapDeterminant_le_exp K hF).trans (Real.exp_le_one_iff.mpr (by linarith))
  have hkernel : sourceOverlapKernel hm a b K ≤
      Real.exp (-sourceTailRate / 4) * overlapDeterminant K ^ (-(1 / 4 : ℝ)) := by
    apply (sourceOverlapKernel_global_bound hm a b hball).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hΔ.le _)
    apply Real.exp_le_exp.mpr
    unfold sourceTailRate
    have hr := sourceLocalRadius_pos
    nlinarith
  have h := source_tail_bound_of_rpow hM (sourceOverlapKernel_nonneg hm a b K) hΔ hΔ1
    (sourceOverlapKernel_polynomial_bound hm a b K) hkernel
  apply h.trans_eq
  have hsub : ((M - 5 : ℕ) : ℝ) = (M : ℝ) - 5 := by rw [Nat.cast_sub hM]; norm_num
  rw [hsub, mul_pow, ← pow_mul]
  have he : ((M : ℝ) - 5) * (4 * (-sourceTailRate / 4)) =
      5 * sourceTailRate + (-sourceTailRate * M) := by ring
  rw [he, Real.exp_add]
  change (Real.exp 1 + 4) ^ 15 * (M : ℝ) ^ 780 *
    (Real.exp (5 * sourceTailRate) * Real.exp (-sourceTailRate * M)) = _
  unfold sourceTailCoefficient
  ring

theorem source_tail_weighted_difference {M : ℕ} (hM : 5 ≤ M)
    (hp : 2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 ≤ sourceLocalRadius ^ 2 / 4000)
    (a b : SourceDensityKind) {K : SourceOverlapMatrix}
    (hball : overlapOperatorNorm K < 1) (hK : sourceLocalRadius < overlapOperatorNorm K) :
    sourceOverlapLebesgueDensity M K * sourceKernelDifference (M := M) (by lia) a b K ≤
      2 * sourceTailCoefficient * (M : ℝ) ^ 784 * Real.exp (-sourceTailRate * M) := by
  have hm : 2 ≤ M := by lia
  have hΔ := (overlapDeterminant_pos hball).le
  have hc := sourceTailCoefficient_pos.le
  have hu := sourceOverlapKernel_nonneg hm a b K
  have hv := sourceOverlapKernel_nonneg hm .reference .reference K
  have hdiff : sourceKernelDifference hm a b K ≤
      sourceOverlapKernel hm a b K ^ sourceRowCount M +
        sourceOverlapKernel hm .reference .reference K ^ sourceRowCount M := by
    apply abs_le.mpr
    constructor <;> nlinarith [pow_nonneg hu (sourceRowCount M), pow_nonneg hv (sourceRowCount M)]
  have hsum := add_le_add (source_tail_power_determinant hM hp a b hball hK)
    (source_tail_power_determinant hM hp .reference .reference hball hK)
  rw [sourceOverlapLebesgueDensity, if_pos hball]
  change sourceOverlapPrefactor M * overlapDeterminant K ^ (M - 4) * _ ≤ _
  calc
    _ ≤ (M : ℝ) ^ 4 * overlapDeterminant K ^ (M - 4) *
        (sourceOverlapKernel hm a b K ^ sourceRowCount M +
          sourceOverlapKernel hm .reference .reference K ^ sourceRowCount M) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right (sourceOverlapPrefactor_le (M := M) (by lia)) (pow_nonneg hΔ _))
        hdiff (abs_nonneg _) (by positivity)
    _ = (M : ℝ) ^ 4 *
        (sourceOverlapKernel hm a b K ^ sourceRowCount M * overlapDeterminant K ^ (M - 4) +
          sourceOverlapKernel hm .reference .reference K ^ sourceRowCount M * overlapDeterminant K ^ (M - 4)) := by ring
    _ ≤ (M : ℝ) ^ 4 *
        (2 * (sourceTailCoefficient * (M : ℝ) ^ 780 * Real.exp (-sourceTailRate * M))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    _ = _ := by ring

theorem source_weighted_difference_majorant {M : ℕ} (hM : 1600 ≤ M)
    (hp : 2 * sourceDelta M + 2 * sourceEpsilon M ^ 2 ≤ sourceLocalRadius ^ 2 / 4000)
    (a b : SourceDensityKind) (K : SourceOverlapMatrix) :
    sourceOverlapLebesgueDensity M K * sourceKernelDifference (M := M) (by lia) a b K ≤
      8 * sourceTaylorConstant * (M : ℝ) ^ 5 * overlapFrobeniusSq K ^ 2 *
        Real.exp (-(1 / 400) * M * overlapFrobeniusSq K) +
      (2 * sourceTailCoefficient * Real.exp 2 * (M : ℝ) ^ 784 * Real.exp (-sourceTailRate * M)) *
        Real.exp (-overlapFrobeniusSq K) := by
  have hR := sourceTaylorConstant_pos.le
  have hc := sourceTailCoefficient_pos.le
  by_cases hball : overlapOperatorNorm K < 1
  · by_cases hlocal : overlapOperatorNorm K ≤ sourceLocalRadius
    · exact (source_local_weighted_difference hM a b hlocal).trans (le_add_of_nonneg_right (by positivity))
    · have ht := source_tail_weighted_difference (by lia : 5 ≤ M) hp a b hball (lt_of_not_ge hlocal)
      have hx : overlapFrobeniusSq K ≤ 2 := (overlapOperatorNorm_lt_one_iff K).mp hball |>.1.le
      have he : 1 ≤ Real.exp 2 * Real.exp (-overlapFrobeniusSq K) := by
        rw [← Real.exp_add]
        exact Real.one_le_exp_iff.mpr (by linarith)
      apply ht.trans
      apply le_trans _ (le_add_of_nonneg_left (by positivity))
      calc
        _ ≤ (2 * sourceTailCoefficient * (M : ℝ) ^ 784 * Real.exp (-sourceTailRate * M)) *
            (Real.exp 2 * Real.exp (-overlapFrobeniusSq K)) := le_mul_of_one_le_right (by positivity) he
        _ = _ := by ring
  · rw [sourceOverlapLebesgueDensity, if_neg hball, zero_mul]
    positivity

end LikelihoodTailBounds

end NLA.FR05
