import NLA.IE21.Definitions
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
Gaussian cutoff and lower-tail foundations for the frozen IE-21 boundary.
The mathematical argument follows Matthew J. Colbrook's retained IE-21/IE-22
manuscript. Formalization: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal RealInnerProductSpace Topology
namespace NLA.IE21

local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal (by norm_num)

private def centralMass (a : ℝ) : ℝ :=
  (gaussianReal 0 1).real {g | |g| ≤ a}

private theorem centralMass_eq_integral {a : ℝ} (ha : 0 ≤ a) :
    centralMass a = ∫ _g in (-a)..a, (1 : ℝ) ∂gaussianReal 0 1 := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  simp only [setIntegral_const, smul_eq_mul, mul_one, centralMass]
  congr 1
  ext g
  simp only [mem_ofPred_eq, abs_le, mem_Icc]

private theorem centralMass_zero : centralMass 0 = 0 := by
  simp [centralMass, measureReal_def]

private theorem centralMass_continuousOn : ContinuousOn centralMass (Ici 0) := by
  have h := (integrable_const (μ := gaussianReal 0 1) (1 : ℝ)).continuous_primitive 0
  apply (h.sub (h.comp continuous_neg)).continuousOn.congr
  intro a ha
  change centralMass a = (∫ _g in (0 : ℝ)..a, (1 : ℝ) ∂gaussianReal 0 1) -
    ∫ _g in (0 : ℝ)..(-a), (1 : ℝ) ∂gaussianReal 0 1
  rw [intervalIntegral.integral_interval_sub_left
    (integrable_const (μ := gaussianReal 0 1) (1 : ℝ)).intervalIntegrable
    (integrable_const (μ := gaussianReal 0 1) (1 : ℝ)).intervalIntegrable]
  exact centralMass_eq_integral ha

private theorem centralMass_strictMonoOn : StrictMonoOn centralMass (Ici 0) := by
  intro a ha b _ hab
  have hpos : 0 < (gaussianReal 0 1).real (Ioo a b) := by
    apply ENNReal.toReal_pos
    · intro hz
      have hv := gaussianReal_absolutelyContinuous' 0 (v := 1) (by norm_num) hz
      exact (ne_of_gt ((Measure.measure_Ioo_pos volume).mpr hab)) hv
    · exact measure_ne_top _ _
  have hd : Disjoint {g : ℝ | |g| ≤ a} (Ioo a b) := by
    refine Set.disjoint_left.mpr ?_
    intro g hg hi
    change |g| ≤ a at hg
    have := (abs_le.mp hg).2
    linarith [hi.1]
  have hs : {g : ℝ | |g| ≤ a} ∪ Ioo a b ⊆ {g : ℝ | |g| ≤ b} := by
    intro g hg
    rcases hg with hg | hg
    · exact le_trans hg hab.le
    · change |g| ≤ b
      rw [abs_of_nonneg (le_trans ha hg.1.le)]
      exact hg.2.le
  have hu := measureReal_mono (μ := gaussianReal 0 1) hs
  rw [measureReal_union hd measurableSet_Ioo] at hu
  change centralMass a + (gaussianReal 0 1).real (Ioo a b) ≤ centralMass b at hu
  linarith

private theorem centralMass_tendsto : Tendsto centralMass atTop (𝓝 1) := by
  let ν := (gaussianReal 0 1).map (fun g : ℝ => |g|)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (by fun_prop)
  have h := tendsto_cdf_atTop ν
  convert h using 1
  ext a
  rw [cdf_eq_real, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  rfl

private theorem exists_gaussian_cutoff (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ a : ℝ, 0 < a ∧ centralMass a = θ := by
  obtain ⟨b, hb, hmass⟩ :=
    ((eventually_gt_atTop (0 : ℝ)).and
      (centralMass_tendsto.eventually (lt_mem_nhds hθ.2))).exists
  have hc := centralMass_continuousOn.mono (show Icc 0 b ⊆ Ici 0 from fun _ hx => hx.1)
  obtain ⟨a, ha, heq⟩ := intermediate_value_Icc hb.le hc
    (show θ ∈ Icc (centralMass 0) (centralMass b) by
      rw [centralMass_zero]
      exact ⟨hθ.1.le, hmass.le⟩)
  refine ⟨a, ?_, heq⟩
  refine lt_of_le_of_ne ha.1 ?_
  intro hz
  subst a
  simp only [centralMass_zero] at heq
  linarith

private theorem gaussianCutoff_eq (θ a : ℝ) (ha : 0 < a) (h : centralMass a = θ) :
    gaussianCutoff θ = a := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨ha.le, h.ge⟩
  · intro b hb
    by_contra hab
    have hba : b < a := lt_of_not_ge hab
    have hlt := centralMass_strictMonoOn hb.1 ha.le hba
    rw [h] at hlt
    exact (not_lt_of_ge hb.2) hlt

/-- The density integral in the canonical definition is the actual Gaussian
truncated second moment, for every value of the cutoff parameter. -/
theorem gaussianTrim_eq_truncated (θ : ℝ) :
    gaussianTrim θ = ∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1 := by
  have hs : MeasurableSet {g : ℝ | |g| ≤ gaussianCutoff θ} := by measurability
  have heq : {g : ℝ | |g| ≤ gaussianCutoff θ} =
      Icc (-gaussianCutoff θ) (gaussianCutoff θ) := by
    ext g
    simp only [mem_ofPred_eq, abs_le, mem_Icc]
  rw [← integral_indicator hs, integral_gaussianReal_eq_integral_smul (by norm_num : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have hf : (fun g : ℝ => gaussianPDFReal 0 1 g *
      {g : ℝ | |g| ≤ gaussianCutoff θ}.indicator (fun g => g ^ 2) g) =
      (Icc (-gaussianCutoff θ) (gaussianCutoff θ)).indicator
        (fun g : ℝ => (1 / Real.sqrt (2 * Real.pi)) *
          (g ^ 2 * Real.exp (-(g ^ 2) / 2))) := by
    funext g
    by_cases hg : g ∈ {g : ℝ | |g| ≤ gaussianCutoff θ}
    · have hg' : g ∈ Icc (-gaussianCutoff θ) (gaussianCutoff θ) := heq ▸ hg
      simp only [indicator_of_mem hg, indicator_of_mem hg', gaussianPDFReal,
        NNReal.coe_one, mul_one, sub_zero, one_div]
      ring
    · have hg' : g ∉ Icc (-gaussianCutoff θ) (gaussianCutoff θ) := heq ▸ hg
      simp only [indicator_of_notMem hg, indicator_of_notMem hg', mul_zero]
  rw [hf, integral_indicator measurableSet_Icc, integral_const_mul]
  rfl

/-- Integrability required for the exact Gaussian second-moment bound. -/
theorem gaussian_square_integrable :
    Integrable (fun g : ℝ => g ^ 2) (gaussianReal 0 1) := by
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq

/-- The untruncated standard Gaussian second moment is exactly one. -/
theorem gaussian_square_integral :
    (∫ g : ℝ, g ^ 2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id'.aemeasurable] at h
  simpa only [integral_id_gaussianReal, sub_zero, NNReal.coe_one] using h

/-- Exact frozen Gaussian-constant target: the infimum-defined cutoff has the
required unique positive quantile, and the canonical integral has its full law semantics. -/
theorem gaussian_constant (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    0 < gaussianCutoff θ ∧
    (gaussianReal 0 1).real {g | |g| ≤ gaussianCutoff θ} = θ ∧
    (∀ a : ℝ, 0 < a → (gaussianReal 0 1).real {g | |g| ≤ a} = θ →
      a = gaussianCutoff θ) ∧
    gaussianTrim θ = ∫ g in {g | |g| ≤ gaussianCutoff θ}, g ^ 2 ∂gaussianReal 0 1 ∧
    0 ≤ gaussianTrim θ ∧ gaussianTrim θ ≤ 1 := by
  obtain ⟨a, ha, hmass⟩ := exists_gaussian_cutoff θ hθ
  have hcut := gaussianCutoff_eq θ a ha hmass
  refine ⟨hcut.symm ▸ ha, ?_, ?_, gaussianTrim_eq_truncated θ, ?_, ?_⟩
  · change centralMass (gaussianCutoff θ) = θ
    rw [hcut]
    exact hmass
  · intro b hb hmassb
    exact (gaussianCutoff_eq θ b hb hmassb).symm
  · rw [gaussianTrim_eq_truncated]
    exact integral_nonneg (fun g => sq_nonneg g)
  · rw [gaussianTrim_eq_truncated, ← gaussian_square_integral]
    exact setIntegral_le_integral gaussian_square_integrable (ae_of_all _ (fun g => sq_nonneg g))

end NLA.IE21
