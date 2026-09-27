import NLA.FR05.SourceParameters
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace NLA.FR05

/-- The radial coordinate in (3.1). -/
def sourceRadiusSq (z : Fin 2 → ℂ) : ℝ :=
  Complex.normSq (z 0) + Complex.normSq (z 1)

def sourceImbalance (z : Fin 2 → ℂ) : ℝ :=
  (Complex.normSq (z 0) - Complex.normSq (z 1)) / sourceRadiusSq z

/-- The normalization constant in (3.1). -/
def sourceRadialNormalizer (M : ℕ) : ℝ :=
  Real.exp (-sourceDelta M) * (1 + sourceEta * sourceDelta M)

/-- The covariance parameter in (3.3). -/
def sourceVariance (M : ℕ) : ℝ :=
  ((1 + sourceEta) * (1 + sourceDelta M) + sourceEta * sourceDelta M ^ 2) /
    (2 * (1 + sourceEta * sourceDelta M))

/-- The planted density (3.1), including its prescribed value at zero. -/
def sourcePlantedDensity (M : ℕ) (z : Fin 2 → ℂ) : ℝ :=
  if z = 0 then 0 else
    if sourceDelta M ≤ sourceRadiusSq z ∧ |sourceImbalance z| ≤ sourceEpsilon M then
      (sourceEta + (1 - sourceEta) / sourceRadiusSq z) /
        (sourceEpsilon M * sourceRadialNormalizer M)
    else 0

/-- The Gaussian reference density (3.4). -/
def sourceReferenceDensity (M : ℕ) (z : Fin 2 → ℂ) : ℝ :=
  (sourceVariance M)⁻¹ ^ 2 *
    Real.exp (-((sourceVariance M)⁻¹ - 1) * sourceRadiusSq z)

theorem sourceRadiusSq_nonneg (z : Fin 2 → ℂ) : 0 ≤ sourceRadiusSq z := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem measurable_sourceRadiusSq : Measurable sourceRadiusSq := by
  unfold sourceRadiusSq
  fun_prop

theorem measurable_sourceImbalance : Measurable sourceImbalance := by
  unfold sourceImbalance sourceRadiusSq
  fun_prop

theorem measurable_sourcePlantedDensity (M : ℕ) :
    Measurable (sourcePlantedDensity M) := by
  unfold sourcePlantedDensity
  apply Measurable.ite (measurableSet_singleton 0) measurable_const
  have habs : Measurable (fun z ↦ |sourceImbalance z|) := by
    simpa only [Real.norm_eq_abs] using measurable_sourceImbalance.norm
  have hcut : MeasurableSet {z | sourceDelta M ≤ sourceRadiusSq z ∧
      |sourceImbalance z| ≤ sourceEpsilon M} :=
    (measurableSet_le measurable_const measurable_sourceRadiusSq).inter
      (measurableSet_le habs measurable_const)
  exact Measurable.ite hcut
    ((measurable_const.add (measurable_const.div measurable_sourceRadiusSq)).div_const _)
    measurable_const

theorem measurable_sourceReferenceDensity (M : ℕ) :
    Measurable (sourceReferenceDensity M) := by
  unfold sourceReferenceDensity
  exact measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_sourceRadiusSq))

theorem sourceRadialNormalizer_pos (M : ℕ) : 0 < sourceRadialNormalizer M := by
  unfold sourceRadialNormalizer sourceDelta sourceEta
  positivity

theorem sourceVariance_pos (M : ℕ) : 0 < sourceVariance M := by
  unfold sourceVariance sourceDelta sourceEta
  positivity

theorem sourcePlantedDensity_nonneg (M : ℕ) (z : Fin 2 → ℂ) :
    0 ≤ sourcePlantedDensity M z := by
  unfold sourcePlantedDensity
  split_ifs
  · exact le_rfl
  · have hS := sourceRadiusSq_nonneg z
    have hc := sourceRadialNormalizer_pos M
    have hη := sourceEta_pos
    have hη' := sourceEta_lt_one
    have hε : 0 ≤ sourceEpsilon M := by unfold sourceEpsilon; positivity
    positivity
  · exact le_rfl

theorem sourceReferenceDensity_pos (M : ℕ) (z : Fin 2 → ℂ) :
    0 < sourceReferenceDensity M z := by
  unfold sourceReferenceDensity
  have hv := sourceVariance_pos M
  positivity

theorem sourceDelta_le_one {M : ℕ} (hM : 1 ≤ M) : sourceDelta M ≤ 1 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  unfold sourceDelta
  exact inv_le_one_of_one_le₀ (by nlinarith)

theorem sourceVariance_lower (M : ℕ) : (1 + sourceEta) / 2 ≤ sourceVariance M := by
  have hd : 0 ≤ sourceDelta M := by unfold sourceDelta; positivity
  have hden : 0 < 2 * (1 + sourceEta * sourceDelta M) := by
    have := sourceEta_pos
    positivity
  apply (le_div_iff₀ hden).mpr
  norm_num [sourceEta]
  nlinarith [sq_nonneg (sourceDelta M)]

theorem sourceVariance_le_one {M : ℕ} (hM : 2 ≤ M) : sourceVariance M ≤ 1 := by
  have hm : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hd : 0 ≤ sourceDelta M := by unfold sourceDelta; positivity
  have hd' : sourceDelta M ≤ 1 / 4 := by
    unfold sourceDelta
    apply (inv_le_iff_one_le_mul₀ (by positivity : 0 < (M : ℝ) ^ 2)).mpr
    nlinarith
  have hden : 0 < 2 * (1 + sourceEta * sourceDelta M) := by
    have := sourceEta_pos
    positivity
  apply (div_le_iff₀ hden).mpr
  norm_num [sourceEta]
  nlinarith [mul_nonneg hd (sub_nonneg.mpr hd')]

theorem sourceReferenceDensity_le_four {M : ℕ} (hM : 2 ≤ M) (z : Fin 2 → ℂ) :
    sourceReferenceDensity M z ≤ 4 := by
  have hv := sourceVariance_pos M
  have hlo := sourceVariance_lower M
  have hhi := sourceVariance_le_one hM
  have hinv : (sourceVariance M)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hv).mpr
    norm_num [sourceEta] at hlo
    linarith
  have hinv' : 1 ≤ (sourceVariance M)⁻¹ := (one_le_inv₀ hv).mpr hhi
  have hexp : Real.exp (-((sourceVariance M)⁻¹ - 1) * sourceRadiusSq z) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sourceRadiusSq_nonneg z)
  unfold sourceReferenceDensity
  calc
    _ ≤ (sourceVariance M)⁻¹ ^ 2 * 1 := mul_le_mul_of_nonneg_left hexp (sq_nonneg _)
    _ ≤ 4 := by nlinarith [inv_nonneg.mpr hv.le]


theorem sourceRadialNormalizer_lower {M : ℕ} (hM : 1 ≤ M) :
    Real.exp (-1) ≤ sourceRadialNormalizer M := by
  have hd := sourceDelta_le_one hM
  have hδ : 0 ≤ sourceDelta M := by unfold sourceDelta; positivity
  have hη := sourceEta_pos
  unfold sourceRadialNormalizer
  calc
    _ ≤ Real.exp (-sourceDelta M) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ Real.exp (-sourceDelta M) * (1 + sourceEta * sourceDelta M) := by
      nlinarith [Real.exp_pos (-sourceDelta M), mul_nonneg hη.le hδ]

theorem sourcePlantedDensity_le {M : ℕ} (hM : 1 ≤ M) (z : Fin 2 → ℂ) :
    sourcePlantedDensity M z ≤ Real.exp 1 * (M : ℝ) ^ 52 := by
  have hm : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hmpos : 0 < (M : ℝ) := by linarith
  have hε := sourceEpsilon_pos M hM
  have hc := sourceRadialNormalizer_pos M
  have hc' := sourceRadialNormalizer_lower hM
  unfold sourcePlantedDensity
  split_ifs with hz hs
  · positivity
  · have hS : 0 < sourceRadiusSq z :=
      (sourceDelta_pos M hM).trans_le hs.1
    have hiS : (sourceRadiusSq z)⁻¹ ≤ (M : ℝ) ^ 2 := by
      apply (inv_le_iff_one_le_mul₀ hS).mpr
      have hd := hs.1
      unfold sourceDelta at hd
      have hpow : 0 < (M : ℝ) ^ 2 := by positivity
      have := (inv_le_iff_one_le_mul₀ hpow).mp hd
      nlinarith
    have hnum :
        sourceEta + (1 - sourceEta) / sourceRadiusSq z ≤ (M : ℝ) ^ 2 := by
      have hη := sourceEta_pos
      have hη' := sourceEta_lt_one
      rw [div_eq_mul_inv]
      nlinarith [mul_le_mul_of_nonneg_left hiS (sub_nonneg.mpr hη'.le),
        sq_nonneg ((M : ℝ) - 1)]
    have hden : 0 < sourceEpsilon M * sourceRadialNormalizer M := mul_pos hε hc
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (M : ℝ) ^ 2 := hnum
      _ = Real.exp 1 * (M : ℝ) ^ 52 * (sourceEpsilon M * Real.exp (-1)) := by
        unfold sourceEpsilon
        rw [show (52 : ℕ) = 50 + 2 from rfl, pow_add]
        have hexp : Real.exp 1 * Real.exp (-1) = 1 := by
          rw [← Real.exp_add]; norm_num
        field_simp
        nlinarith [hexp]
      _ ≤ Real.exp 1 * (M : ℝ) ^ 52 *
          (sourceEpsilon M * sourceRadialNormalizer M) := by
        gcongr
  · positivity

theorem tendsto_sourceDelta :
    Tendsto sourceDelta atTop (𝓝 0) := by
  change Tendsto (fun M : ℕ ↦ ((M : ℝ) ^ 2)⁻¹) atTop (𝓝 0)
  exact
    ((tendsto_pow_atTop (α := ℝ) (by norm_num : 2 ≠ 0)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop

theorem tendsto_sourceVariance :
    Tendsto sourceVariance atTop (𝓝 ((1 + sourceEta) / 2)) := by
  have hn : Tendsto
      (fun M ↦ (1 + sourceEta) * (1 + sourceDelta M) + sourceEta * sourceDelta M ^ 2)
      atTop (𝓝 ((1 + sourceEta) * (1 + 0) + sourceEta * 0 ^ 2)) :=
    ((tendsto_const_nhds.mul ((tendsto_const_nhds (x := (1 : ℝ))).add
      tendsto_sourceDelta)).add (tendsto_const_nhds.mul (tendsto_sourceDelta.pow 2)))
  have hd : Tendsto (fun M ↦ 2 * (1 + sourceEta * sourceDelta M))
      atTop (𝓝 (2 * (1 + sourceEta * 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.add
      (tendsto_const_nhds.mul tendsto_sourceDelta))
  change Tendsto (fun M ↦
    ((1 + sourceEta) * (1 + sourceDelta M) + sourceEta * sourceDelta M ^ 2) /
      (2 * (1 + sourceEta * sourceDelta M))) atTop (𝓝 ((1 + sourceEta) / 2))
  simpa only [Pi.div_def, add_zero, mul_zero, zero_pow (by norm_num : 2 ≠ 0), mul_one] using
    hn.div hd (by norm_num)

/-- A uniform gap is already available at M = 2; no limiting threshold is needed. -/
theorem source_covariance_gap {M : ℕ} (hM : 2 ≤ M) :
    4 * (1 - sourceVariance M) ^ 2 ≤ (1 - sourceEta) ^ 2 := by
  have hlo := sourceVariance_lower M
  have hhi := sourceVariance_le_one hM
  norm_num [sourceEta] at *
  nlinarith

end NLA.FR05
