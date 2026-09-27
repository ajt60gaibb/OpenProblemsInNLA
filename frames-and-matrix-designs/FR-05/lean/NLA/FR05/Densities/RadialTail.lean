/-
The radial part of the source tail estimate in (3.22).

The density in (3.2) is represented exactly as a mixture of an exponential
law and a Gamma(2,1) law, followed by conditioning on `S ≥ δ`.  This file
proves a stand-alone exponential tail bound for that scalar coordinate.
-/
import NLA.FR05.Densities.PlantedLaw
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal BigOperators

namespace NLA.FR05

/-- Density measures have no atoms, so open and closed lower rays agree for
the exponential law. -/
theorem radial_expMeasure_Iio_eq_Iic (r t : ℝ) :
    expMeasure r (Iio t) = expMeasure r (Iic t) := by
  have hatom : expMeasure r ({t} : Set ℝ) = 0 := by
    exact withDensity_absolutelyContinuous volume (gammaPDF 1 r)
      Real.volume_singleton
  have hd : Disjoint (Iio t) ({t} : Set ℝ) := by
    refine Set.disjoint_left.2 ?_
    intro x hlt hEq
    exact (ne_of_lt hlt) hEq
  rw [← Iio_union_right,
    MeasureTheory.measure_union hd (measurableSet_singleton t)]
  rw [hatom, add_zero]

/-- Exact upper-ray probability for an exponential law. -/
theorem radial_expMeasure_apply_Ici (r t : ℝ) (hr : 0 < r) (ht : 0 ≤ t) :
    expMeasure r (Ici t) = ENNReal.ofReal (Real.exp (-(r * t))) := by
  let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← Set.compl_Iio]
  rw [MeasureTheory.measure_compl measurableSet_Iio (measure_ne_top _ _)]
  rw [measure_univ]
  rw [radial_expMeasure_Iio_eq_Iic]
  rw [← ofReal_cdf]
  rw [cdf_expMeasure_eq hr]
  rw [if_pos ht]
  rw [ENNReal.ofReal_sub 1 (by positivity)]
  rw [← ENNReal.ofReal_one]
  apply ENNReal.sub_sub_cancel (by norm_num)
  apply ENNReal.ofReal_le_ofReal
  rw [Real.exp_le_one_iff]
  have hnonneg : 0 ≤ r * t := mul_nonneg hr.le ht
  linarith

/-- Pointwise domination of the Gamma(2,1) density by four times an
exponential density of rate one half. -/
theorem radial_gammaMeasure_two_one_le_four_smul_expHalf :
    gammaMeasure 2 1 ≤ (4 : ℝ≥0∞) • expMeasure (1 / 2) := by
  have hmeas : Measurable (gammaPDF (1 : ℝ) (1 / 2)) :=
    (measurable_gammaPDFReal 1 (1 / 2)).ennreal_ofReal
  change volume.withDensity (gammaPDF 2 1) ≤
    (4 : ℝ≥0∞) • volume.withDensity (gammaPDF 1 (1 / 2))
  rw [← withDensity_smul (4 : ℝ≥0∞) hmeas]
  apply withDensity_mono
  filter_upwards [] with x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [gammaPDF_eq 2 1 x, gammaPDF_eq 1 (1 / 2) x]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx, if_pos hx]
    norm_num [Real.Gamma_nat_eq_factorial]
    have hscale (y : ℝ) (hy : 0 ≤ y) :
        (4 : ℝ≥0∞) * (ENNReal.ofReal (1 / 2) * ENNReal.ofReal y) =
          ENNReal.ofReal (2 * y) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
        norm_num
      have hcoeff : (2 : ℝ≥0∞)⁻¹ * 4 = 2 := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ← mul_assoc,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
        simp
      rw [hhalf]
      norm_num only [ENNReal.ofReal_ofNat]
      simp only [div_eq_mul_inv, one_mul]
      change (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal y) =
        (2 : ℝ≥0∞) * ENNReal.ofReal y
      calc
        (4 : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal y) =
            ((2 : ℝ≥0∞)⁻¹ * 4) * ENNReal.ofReal y := by ring
        _ = 2 * ENNReal.ofReal y := by rw [hcoeff]
    have hreal : x * Real.exp (-x) ≤ 2 * Real.exp (-(1 / 2 * x)) := by
      have hbase : (x / 2) * Real.exp (-(x / 2)) ≤ 1 := by
        calc
          (x / 2) * Real.exp (-(x / 2)) ≤ Real.exp (-1) :=
            Real.mul_exp_neg_le_exp_neg_one _
          _ ≤ 1 := by
            rw [← Real.exp_zero]
            exact Real.exp_le_exp.mpr (by norm_num)
      calc
        x * Real.exp (-x) =
            (2 * ((x / 2) * Real.exp (-(x / 2)))) * Real.exp (-(x / 2)) := by
          have hExp : Real.exp (-x) =
              Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
          rw [hExp]
          ring
        _ ≤ (2 * 1) * Real.exp (-(x / 2)) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hbase (by norm_num)
          · exact (Real.exp_pos _).le
        _ = 2 * Real.exp (-(1 / 2 * x)) := by ring_nf
    calc
      ENNReal.ofReal (x * Real.exp (-x)) ≤
          ENNReal.ofReal (2 * Real.exp (-(1 / 2 * x))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = (4 : ℝ≥0∞) *
          (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.exp (-(1 / 2 * x)))) :=
        (hscale _ (Real.exp_pos _).le).symm
  · rw [if_neg hx, if_neg hx]
    simp

/-- A measure-level Gamma(2,1) tail bound. -/
theorem radial_gammaMeasure_two_one_apply_Ici_le (t : ℝ) (ht : 0 ≤ t) :
    gammaMeasure 2 1 (Ici t) ≤
      (4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t))) := by
  calc
    gammaMeasure 2 1 (Ici t) ≤ ((4 : ℝ≥0∞) • expMeasure (1 / 2)) (Ici t) :=
      radial_gammaMeasure_two_one_le_four_smul_expHalf (Ici t)
    _ = (4 : ℝ≥0∞) * expMeasure (1 / 2) (Ici t) := by
      rw [Measure.smul_apply]
      simp only [smul_eq_mul]
    _ = (4 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t))) := by
      rw [radial_expMeasure_apply_Ici (1 / 2) t (by norm_num) ht]

/-- The unconditioned source mixture has a uniform exponential tail. -/
theorem sourceRadialBase_apply_Ici_le_five_expHalf
    {η t : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht : 0 ≤ t) :
    sourceRadialBase η (Ici t) ≤
      (5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t))) := by
  let z : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(1 / 2 * t)))
  have hweightOne : ENNReal.ofReal (1 - η) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hweightTwo : ENNReal.ofReal η ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal hη1
  have hExpOne : expMeasure 1 (Ici t) ≤ z := by
    rw [radial_expMeasure_apply_Ici 1 t (by norm_num) ht]
    change ENNReal.ofReal (Real.exp (-(1 * t))) ≤
      ENNReal.ofReal (Real.exp (-(1 / 2 * t)))
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  have hGamma : gammaMeasure 2 1 (Ici t) ≤ 4 * z := by
    simpa only [z] using radial_gammaMeasure_two_one_apply_Ici_le t ht
  have hfirst : ENNReal.ofReal (1 - η) * expMeasure 1 (Ici t) ≤ z := by
    calc
      ENNReal.ofReal (1 - η) * expMeasure 1 (Ici t) ≤
          ENNReal.ofReal (1 - η) * z :=
        mul_le_mul_of_nonneg_left hExpOne bot_le
      _ ≤ 1 * z := mul_le_mul_of_nonneg_right hweightOne bot_le
      _ = z := one_mul _
  have hsecond : ENNReal.ofReal η * gammaMeasure 2 1 (Ici t) ≤ 4 * z := by
    calc
      ENNReal.ofReal η * gammaMeasure 2 1 (Ici t) ≤
          ENNReal.ofReal η * (4 * z) :=
        mul_le_mul_of_nonneg_left hGamma bot_le
      _ ≤ 1 * (4 * z) := mul_le_mul_of_nonneg_right hweightTwo bot_le
      _ = 4 * z := one_mul _
  calc
    sourceRadialBase η (Ici t) =
        ENNReal.ofReal (1 - η) * expMeasure 1 (Ici t) +
          ENNReal.ofReal η * gammaMeasure 2 1 (Ici t) := by
      simp [sourceRadialBase]
    _ ≤ z + 4 * z := add_le_add hfirst hsecond
    _ = 5 * z := by ring

/-- Exact upper-ray evaluation for the source radial law after conditioning. -/
theorem sourceRadialLaw_apply_Ici_eq_base
    {η δ t : ℝ} (hδt : δ ≤ t) :
    sourceRadialLaw η δ (Ici t) =
      (sourceRadialBase η (Ici δ))⁻¹ * sourceRadialBase η (Ici t) := by
  unfold sourceRadialLaw
  rw [ProbabilityTheory.cond_apply measurableSet_Ici]
  have hinter : Ici δ ∩ Ici t = Ici t := by
    ext x
    simp only [mem_inter_iff, mem_Ici]
    constructor
    · intro hx
      exact hx.2
    · intro hx
      exact ⟨hδt.trans hx, hx⟩
  rw [hinter]

/-- Source-faithful radial tail bound with the conditioning normalizer still
explicit. -/
theorem sourceRadialLaw_apply_Ici_le_normalized
    {η δ t : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hδt : δ ≤ t) (ht : 0 ≤ t) :
    sourceRadialLaw η δ (Ici t) ≤
      (sourceRadialBase η (Ici δ))⁻¹ *
        ((5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t)))) := by
  rw [sourceRadialLaw_apply_Ici_eq_base hδt]
  apply mul_le_mul_of_nonneg_left
  exact sourceRadialBase_apply_Ici_le_five_expHalf hη0 hη1 ht
  exact bot_le

/-- At the manuscript's fixed mixture weight, conditioning at a cutoff at
most one retains at least one fifth of the base radial mass. -/
theorem one_fifth_le_sourceRadialBase_sourceEta_Ici
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 / 5 : ℝ≥0∞) ≤ sourceRadialBase sourceEta (Ici δ) := by
  have hquarter : (1 / 4 : ℝ) ≤ Real.exp (-δ) := by
    exact (calc
      (1 / 4 : ℝ) < 0.36787944116 := by norm_num
      _ < Real.exp (-1) := Real.exp_neg_one_gt_d9
      _ ≤ Real.exp (-δ) := by
        apply Real.exp_le_exp.mpr
        linarith).le
  have htail : expMeasure 1 (Ici δ) = ENNReal.ofReal (Real.exp (-δ)) := by
    simpa using radial_expMeasure_apply_Ici 1 δ (by norm_num) hδ0
  have hmain : (1 / 5 : ℝ≥0∞) ≤
      ENNReal.ofReal (1 - sourceEta) * expMeasure 1 (Ici δ) := by
    rw [htail]
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr sourceEta_lt_one.le)]
    have hOneFifth : ENNReal.ofReal (1 / 5 : ℝ) = (1 / 5 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 5)]
      norm_num
    rw [← hOneFifth]
    apply ENNReal.ofReal_le_ofReal
    dsimp [sourceEta]
    nlinarith
  calc
    (1 / 5 : ℝ≥0∞) ≤
        ENNReal.ofReal (1 - sourceEta) * expMeasure 1 (Ici δ) := hmain
    _ ≤ ENNReal.ofReal (1 - sourceEta) * expMeasure 1 (Ici δ) +
        ENNReal.ofReal sourceEta * gammaMeasure 2 1 (Ici δ) :=
      le_add_of_nonneg_right bot_le
    _ = sourceRadialBase sourceEta (Ici δ) := by
      simp [sourceRadialBase]

/-- Uniform radial tail for the manuscript's fixed conditioned mixture. -/
theorem sourceRadialLaw_sourceEta_apply_Ici_le_twentyFive_expHalf
    {δ t : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hδt : δ ≤ t) (ht : 0 ≤ t) :
    sourceRadialLaw sourceEta δ (Ici t) ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t))) := by
  have hden : (1 / 5 : ℝ≥0∞) ≤ sourceRadialBase sourceEta (Ici δ) :=
    one_fifth_le_sourceRadialBase_sourceEta_Ici hδ0 hδ1
  have hinv : (sourceRadialBase sourceEta (Ici δ))⁻¹ ≤ (5 : ℝ≥0∞) := by
    calc
      (sourceRadialBase sourceEta (Ici δ))⁻¹ ≤ (1 / 5 : ℝ≥0∞)⁻¹ :=
        ENNReal.inv_le_inv.mpr hden
      _ = 5 := by norm_num
  calc
    sourceRadialLaw sourceEta δ (Ici t) ≤
        (sourceRadialBase sourceEta (Ici δ))⁻¹ *
          ((5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t)))) :=
      sourceRadialLaw_apply_Ici_le_normalized
        sourceEta_pos.le sourceEta_lt_one.le hδt ht
    _ ≤ 5 * ((5 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t)))) :=
      mul_le_mul_of_nonneg_right hinv bot_le
    _ = (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(1 / 2 * t))) := by ring

theorem sourceDelta_nonneg_le_one {M : ℕ} (hM : 1 ≤ M) :
    0 ≤ sourceDelta M ∧ sourceDelta M ≤ 1 := by
  have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hsq : 1 ≤ (M : ℝ) ^ 2 := by nlinarith
  unfold sourceDelta
  constructor
  · exact inv_nonneg.mpr (by positivity)
  · exact inv_le_one_of_one_le₀ hsq

theorem sourceDelta_le_eight_mul {M : ℕ} (hM : 1 ≤ M) :
    sourceDelta M ≤ 8 * (M : ℝ) := by
  have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  calc
    sourceDelta M ≤ 1 := (sourceDelta_nonneg_le_one hM).2
    _ ≤ 8 * (M : ℝ) := by nlinarith

/-- The radial coordinate in the source planted law at the Proposition 3.1
scale obeys an explicit exponentially small tail bound. -/
theorem sourceRadialLaw_sourceM_apply_Ici_le
    {M : ℕ} (hM : 1 ≤ M) :
    sourceRadialLaw sourceEta (sourceDelta M) (Ici (8 * (M : ℝ))) ≤
      (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
  have hδ := sourceDelta_nonneg_le_one hM
  calc
    sourceRadialLaw sourceEta (sourceDelta M) (Ici (8 * (M : ℝ))) ≤
        (25 : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (-(1 / 2 * (8 * (M : ℝ))))) :=
      sourceRadialLaw_sourceEta_apply_Ici_le_twentyFive_expHalf
        hδ.1 hδ.2 (sourceDelta_le_eight_mul hM) (by positivity)
    _ = (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
      congr 3
      ring

end NLA.FR05
