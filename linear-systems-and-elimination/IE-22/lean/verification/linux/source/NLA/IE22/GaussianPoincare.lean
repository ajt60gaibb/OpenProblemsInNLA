import NLA.IE22.Definitions
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.Tactic

/-!
Exact Gaussian variance foundation for IE-22. The scalar interval-energy step
is proved here; finite-product tensorization is proved in VarianceTensorization.
No Poincare inequality is assumed.
Original application: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology
namespace NLA.IE22

/-- The independent-copy formula, with all second moments explicit. -/
theorem variance_eq_half_pair_energy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    Var[f; μ] = (1 / 2 : ℝ) * ∫ x, ∫ y, (f x - f y) ^ 2 ∂μ ∂μ := by
  have hi : Integrable f μ := hf.integrable (by norm_num)
  have hi2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have hinner (x : Ω) : (∫ y, (f x - f y) ^ 2 ∂μ) =
      f x ^ 2 - 2 * f x * (∫ y, f y ∂μ) + ∫ y, f y ^ 2 ∂μ := by
    simp_rw [sub_sq]
    have hlin : Integrable (fun y => 2 * f x * f y) μ := hi.const_mul (2 * f x)
    have hleft : Integrable (fun y => f x ^ 2 - 2 * f x * f y) μ :=
      (integrable_const (f x ^ 2)).sub hlin
    rw [integral_add hleft hi2, integral_sub (integrable_const (f x ^ 2)) hlin,
      integral_const_mul]
    simp
  simp_rw [hinner]
  have hlin : Integrable (fun x => 2 * f x * (∫ y, f y ∂μ)) μ :=
    (hi.const_mul 2).mul_const _
  have hleft : Integrable (fun x => f x ^ 2 - 2 * f x * (∫ y, f y ∂μ)) μ := hi2.sub hlin
  rw [integral_add hleft (integrable_const _), integral_sub hi2 hlin,
    integral_mul_const, integral_const_mul, variance_eq_sub hf]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, Pi.pow_apply]
  ring

/-- The derivative of the literal standard Gaussian density. -/
theorem gaussian_density_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have hd : HasDerivAt (fun z : ℝ => -(z ^ 2) / 2) (-x) x := by
    exact (((hasDerivAt_id x).pow 2).neg.div_const 2).congr_deriv (by norm_num; ring)
  have h := hd.exp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  have heq : gaussianPDFReal 0 1 =
      fun z : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(z ^ 2) / 2) := by
    funext z
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [heq]
  exact h.congr_deriv (by ring)

theorem gaussian_density_tendsto_atTop :
    Tendsto (gaussianPDFReal 0 1) atTop (𝓝 0) := by
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have hexp := Real.tendsto_exp_atBot.comp
    (hpow.const_mul_atTop_of_neg (by norm_num : (-1 / 2 : ℝ) < 0))
  have h := hexp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹)
  convert h using 1
  · ext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    congr 2
    ring
  · simp

theorem gaussian_density_tendsto_atBot :
    Tendsto (gaussianPDFReal 0 1) atBot (𝓝 0) := by
  have h := gaussian_density_tendsto_atTop.comp tendsto_neg_atBot_atTop
  have heq : (gaussianPDFReal 0 1) ∘ (fun x : ℝ => -x) = gaussianPDFReal 0 1 := by
    funext x
    simp [gaussianPDFReal]
  rwa [heq] at h

theorem gaussian_density_first_moment_integrable :
    Integrable (fun x : ℝ => x * gaussianPDFReal 0 1 x) := by
  have heq (x : ℝ) : x * gaussianPDFReal 0 1 x =
      (Real.sqrt (2 * Real.pi))⁻¹ * (x * Real.exp (-(1 / 2 : ℝ) * x ^ 2)) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [show -(x ^ 2) / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  simp_rw [heq]
  exact (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _

/-- Right truncated first moment of the density. -/
theorem gaussian_density_right_first_moment (a : ℝ) :
    ∫ x in Ioi a, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 a := by
  have hd (x : ℝ) : HasDerivAt (fun z => -gaussianPDFReal 0 1 z)
      (x * gaussianPDFReal 0 1 x) x := by
    simpa using! (gaussian_density_hasDerivAt x).neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => hd x) gaussian_density_first_moment_integrable.integrableOn
    gaussian_density_tendsto_atTop.neg
  simpa using h

/-- Left truncated first moment of the density. -/
theorem gaussian_density_left_first_moment (a : ℝ) :
    ∫ x in Iic a, x * gaussianPDFReal 0 1 x = -gaussianPDFReal 0 1 a := by
  have hd (x : ℝ) : HasDerivAt (fun z => -gaussianPDFReal 0 1 z)
      (x * gaussianPDFReal 0 1 x) x := by
    simpa using! (gaussian_density_hasDerivAt x).neg
  have h := integral_Iic_of_hasDerivAt_of_tendsto'
    (a := a) (fun x _ => hd x) gaussian_density_first_moment_integrable.integrableOn
    gaussian_density_tendsto_atBot.neg
  simpa using h

/-- Density transport, also for a restricted set. -/
theorem gaussian_setIntegral_density (s : Set ℝ) (hs : MeasurableSet s) (f : ℝ → ℝ) :
    ∫ x in s, f x ∂gaussianReal 0 1 =
      ∫ x in s, gaussianPDFReal 0 1 x * f x := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    restrict_withDensity hs]
  simpa [gaussianPDF_def, gaussianPDFReal_nonneg] using
    integral_withDensity_eq_integral_toReal_smul (μ := volume.restrict s)
      (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top) f

theorem gaussian_right_first_moment (a : ℝ) :
    ∫ x in Ioi a, x ∂gaussianReal 0 1 = gaussianPDFReal 0 1 a := by
  rw [gaussian_setIntegral_density _ measurableSet_Ioi]
  simpa only [mul_comm] using gaussian_density_right_first_moment a

theorem gaussian_left_first_moment (a : ℝ) :
    ∫ x in Iic a, x ∂gaussianReal 0 1 = -gaussianPDFReal 0 1 a := by
  rw [gaussian_setIntegral_density _ measurableSet_Iic]
  simpa only [mul_comm] using gaussian_density_left_first_moment a

/-- The crossing kernel equals the density exactly; this is the source of the
constant one in the scalar Gaussian Poincare inequality. -/
theorem gaussian_crossing_kernel (a : ℝ) :
    (∫ x in Iic a, ∫ y in Ioi a, (y - x) ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      gaussianPDFReal 0 1 a := by
  let μ := gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => x) μ :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hinner (x : ℝ) : (∫ y in Ioi a, y - x ∂μ) =
      gaussianPDFReal 0 1 a - μ.real (Ioi a) * x := by
    rw [integral_sub hi.integrableOn (integrable_const x), gaussian_right_first_moment]
    simp only [setIntegral_const, smul_eq_mul]
  change (∫ x in Iic a, ∫ y in Ioi a, (y - x) ∂μ ∂μ) = gaussianPDFReal 0 1 a
  simp_rw [hinner]
  rw [integral_sub (integrable_const _) (hi.integrableOn.const_mul _),
    integral_const_mul, gaussian_left_first_moment]
  simp only [setIntegral_const, smul_eq_mul]
  have hmass : μ.real (Iic a) + μ.real (Ioi a) = 1 := by
    have h := integral_add_compl (μ := μ) (f := fun _ : ℝ => (1 : ℝ))
      (s := Iic a) measurableSet_Iic (integrable_const 1)
    simpa using h
  calc
    _ = (μ.real (Iic a) + μ.real (Ioi a)) * gaussianPDFReal 0 1 a := by ring
    _ = gaussianPDFReal 0 1 a := by rw [hmass, one_mul]

/-- Nonnegative crossing weight used for Tonelli, including only the ordered
crossing `x ≤ s < y`. Endpoints have no effect on the scalar Lebesgue integral. -/
def gaussianCrossingWeight (x y s : ℝ) : ℝ≥0∞ :=
  if x ≤ s ∧ s < y then ENNReal.ofReal (y - x) else 0

theorem gaussian_crossing_weight_measurable :
    Measurable (fun p : ℝ × ℝ × ℝ => gaussianCrossingWeight p.1 p.2.1 p.2.2) := by
  unfold gaussianCrossingWeight
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

@[fun_prop]
theorem measurable_gaussianCrossingWeight {Ω : Type*} [MeasurableSpace Ω]
    (x y s : Ω → ℝ) (hx : Measurable x) (hy : Measurable y) (hs : Measurable s) :
    Measurable (fun ω => gaussianCrossingWeight (x ω) (y ω) (s ω)) := by
  unfold gaussianCrossingWeight
  exact Measurable.ite ((measurableSet_le hx hs).inter (measurableSet_lt hs hy))
    ((hy.sub hx).ennreal_ofReal) measurable_const

/-- Tonelli form of the exact crossing kernel. -/
theorem gaussian_crossing_kernel_lintegral (a : ℝ) :
    (∫⁻ x, ∫⁻ y, gaussianCrossingWeight x y a ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      ENNReal.ofReal (gaussianPDFReal 0 1 a) := by
  let μ := gaussianReal 0 1
  have hi : Integrable (fun x : ℝ => x) μ :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hinner (x : ℝ) : (∫ y in Ioi a, y - x ∂μ) =
      gaussianPDFReal 0 1 a - μ.real (Ioi a) * x := by
    rw [integral_sub hi.integrableOn (integrable_const x), gaussian_right_first_moment]
    simp only [setIntegral_const, smul_eq_mul]
  have houter : Integrable (fun x : ℝ => ∫ y in Ioi a, y - x ∂μ) (μ.restrict (Iic a)) := by
    simp_rw [hinner]
    exact (integrable_const _).sub (hi.integrableOn.const_mul _)
  have hnn (x : ℝ) (hx : x ≤ a) :
      0 ≤ᵐ[μ.restrict (Ioi a)] fun y => y - x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact sub_nonneg.mpr (hx.trans hy.le)
  have heq (x y : ℝ) : gaussianCrossingWeight x y a =
      (Iic a).indicator (fun x => (Ioi a).indicator (fun y => ENNReal.ofReal (y - x)) y) x := by
    simp only [gaussianCrossingWeight, Set.indicator, mem_Iic, mem_Ioi]
    split_ifs <;> simp_all
  change (∫⁻ x, ∫⁻ y, gaussianCrossingWeight x y a ∂μ ∂μ) = _
  simp_rw [heq]
  have hinner_indicator (x : ℝ) :
      (∫⁻ y, (Iic a).indicator
        (fun x => (Ioi a).indicator (fun y => ENNReal.ofReal (y - x)) y) x ∂μ) =
      (Iic a).indicator (fun x => ∫⁻ y in Ioi a, ENNReal.ofReal (y - x) ∂μ) x := by
    by_cases hx : x ∈ Iic a
    · simp only [indicator_of_mem hx, lintegral_indicator measurableSet_Ioi]
    · simp only [indicator_of_notMem hx, lintegral_zero]
  simp_rw [hinner_indicator]
  rw [lintegral_indicator measurableSet_Iic]
  calc
    (∫⁻ x in Iic a, ∫⁻ y in Ioi a, ENNReal.ofReal (y - x) ∂μ ∂μ) =
        ∫⁻ x in Iic a, ENNReal.ofReal (∫ y in Ioi a, y - x ∂μ) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact (ofReal_integral_eq_lintegral_ofReal
        (hi.integrableOn.sub (integrable_const x)) (hnn x hx)).symm
    _ = ENNReal.ofReal (∫ x in Iic a, ∫ y in Ioi a, y - x ∂μ ∂μ) := by
      apply (ofReal_integral_eq_lintegral_ofReal houter ?_).symm
      filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
      exact integral_nonneg_of_ae (hnn x hx)
    _ = ENNReal.ofReal (gaussianPDFReal 0 1 a) := by
      rw [gaussian_crossing_kernel]

/-- Exact integral identity for a nonnegative energy density. Tonelli supplies
all rearrangements, so this statement also permits infinite energy. -/
theorem gaussian_crossing_energy (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ x, ∫⁻ y, ∫⁻ s, H s * gaussianCrossingWeight x y s
      ∂volume ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      ∫⁻ s, H s ∂gaussianReal 0 1 := by
  have hswap (x : ℝ) :
      (∫⁻ y, ∫⁻ s, H s * gaussianCrossingWeight x y s ∂volume ∂gaussianReal 0 1) =
      ∫⁻ s, ∫⁻ y, H s * gaussianCrossingWeight x y s ∂gaussianReal 0 1 ∂volume :=
    lintegral_lintegral_swap (by fun_prop)
  simp_rw [hswap]
  have hm : Measurable (fun p : ℝ × ℝ =>
      ∫⁻ y, H p.2 * gaussianCrossingWeight p.1 y p.2 ∂gaussianReal 0 1) := by
    exact Measurable.lintegral_prod_right' (f := fun q : (ℝ × ℝ) × ℝ =>
      H q.1.2 * gaussianCrossingWeight q.1.1 q.2 q.1.2) (by fun_prop)
  rw [lintegral_lintegral_swap hm.aemeasurable]
  have hfactor (s : ℝ) :
      (∫⁻ x, ∫⁻ y, H s * gaussianCrossingWeight x y s
        ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      H s * ENNReal.ofReal (gaussianPDFReal 0 1 s) := by
    have hi (x : ℝ) :
        (∫⁻ y, H s * gaussianCrossingWeight x y s ∂gaussianReal 0 1) =
        H s * ∫⁻ y, gaussianCrossingWeight x y s ∂gaussianReal 0 1 :=
      lintegral_const_mul (H s) (by fun_prop)
    simp_rw [hi]
    rw [lintegral_const_mul (H s) (Measurable.lintegral_prod_right
      (by fun_prop : Measurable (Function.uncurry (fun x y : ℝ =>
        gaussianCrossingWeight x y s)))), gaussian_crossing_kernel_lintegral]
  simp_rw [hfactor]
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    lintegral_withDensity_eq_lintegral_mul volume (measurable_gaussianPDF 0 1) hH]
  apply lintegral_congr
  intro s
  simp only [Pi.mul_apply, gaussianPDF_def, mul_comm]

/-- Pair energy as a nonnegative integral; the factor two is exact. -/
theorem gaussian_pair_energy_lintegral (f : ℝ → ℝ)
    (hf : MemLp f 2 (gaussianReal 0 1)) :
    (∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((f p.1 - f p.2) ^ 2)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) =
      2 * ENNReal.ofReal (Var[f; gaussianReal 0 1]) := by
  have hp : Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) ^ 2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    ((hf.comp_fst _).sub (hf.comp_snd _)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hp (ae_of_all _ fun p => sq_nonneg _),
    integral_prod _ hp]
  have heq : (∫ x, ∫ y, (f x - f y) ^ 2 ∂gaussianReal 0 1 ∂gaussianReal 0 1) =
      2 * Var[f; gaussianReal 0 1] := by
    rw [variance_eq_half_pair_energy _ f hf]
    ring
  rw [heq, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Scalar Gaussian variance bound from an explicit pairwise crossing-energy
estimate. This is proved from the literal Gaussian density and Tonelli. -/
theorem gaussian_variance_le_of_crossing_bound (f : ℝ → ℝ)
    (hf : MemLp f 2 (gaussianReal 0 1))
    (H : ℝ → ℝ≥0∞) (hH : Measurable H)
    (hbound : ∀ x y : ℝ, ENNReal.ofReal ((f x - f y) ^ 2) ≤
      (∫⁻ s, H s * gaussianCrossingWeight x y s) +
      ∫⁻ s, H s * gaussianCrossingWeight y x s) :
    ENNReal.ofReal (Var[f; gaussianReal 0 1]) ≤ ∫⁻ s, H s ∂gaussianReal 0 1 := by
  let μ := gaussianReal 0 1
  let G (p : ℝ × ℝ) := ∫⁻ s, H s * gaussianCrossingWeight p.1 p.2 s
  have hG : Measurable G := Measurable.lintegral_prod_right'
    (f := fun q : (ℝ × ℝ) × ℝ => H q.2 * gaussianCrossingWeight q.1.1 q.1.2 q.2)
    (by fun_prop)
  have henergy : (∫⁻ p, G p ∂μ.prod μ) = ∫⁻ s, H s ∂μ := by
    rw [lintegral_prod _ hG.aemeasurable]
    exact gaussian_crossing_energy H hH
  have hle : 2 * ENNReal.ofReal (Var[f; μ]) ≤ 2 * ∫⁻ s, H s ∂μ := by
    calc
      _ = ∫⁻ p : ℝ × ℝ, ENNReal.ofReal ((f p.1 - f p.2) ^ 2) ∂μ.prod μ :=
        (gaussian_pair_energy_lintegral f hf).symm
      _ ≤ ∫⁻ p, G p + G p.swap ∂μ.prod μ := lintegral_mono (fun p => hbound p.1 p.2)
      _ = (∫⁻ p, G p ∂μ.prod μ) + ∫⁻ p, G p.swap ∂μ.prod μ :=
        lintegral_add_left hG _
      _ = 2 * ∫⁻ s, H s ∂μ := by
        rw [lintegral_prod_swap, henergy, two_mul]
  exact (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).mp hle

/-- The crossing integral is the interval energy in its original real form. -/
theorem gaussian_crossing_square_energy (D : ℝ → ℝ) (hD : Measurable D)
    (x y : ℝ) (hxy : x ≤ y)
    (hi : IntegrableOn (fun s => D s ^ 2) (Ico x y)) :
    (∫⁻ s, ENNReal.ofReal (D s ^ 2) * gaussianCrossingWeight x y s) =
      ENNReal.ofReal ((y - x) * ∫ s in Ico x y, D s ^ 2) := by
  have heq (s : ℝ) : ENNReal.ofReal (D s ^ 2) * gaussianCrossingWeight x y s =
      (Ico x y).indicator (fun s =>
        ENNReal.ofReal (y - x) * ENNReal.ofReal (D s ^ 2)) s := by
    simp only [gaussianCrossingWeight, Set.indicator, mem_Ico]
    split_ifs <;> simp [mul_comm]
  simp_rw [heq]
  rw [lintegral_indicator measurableSet_Ico,
    lintegral_const_mul (ENNReal.ofReal (y - x)) ((hD.pow_const 2).ennreal_ofReal),
    ← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun s => sq_nonneg _),
    ENNReal.ofReal_mul (sub_nonneg.mpr hxy)]

/-- Exact-one scalar Gaussian Poincare inequality from interval energy.
Every application must prove its derivative's interval energy separately. -/
theorem gaussian_poincare_of_interval_energy (f D : ℝ → ℝ)
    (hf : MemLp f 2 (gaussianReal 0 1)) (hD : Measurable D)
    (hDγ : Integrable (fun s => D s ^ 2) (gaussianReal 0 1))
    (hinterval : ∀ x y : ℝ, x ≤ y →
      IntegrableOn (fun s => D s ^ 2) (Ico x y) ∧
      (f y - f x) ^ 2 ≤ (y - x) * ∫ s in Ico x y, D s ^ 2) :
    Var[f; gaussianReal 0 1] ≤ ∫ s, D s ^ 2 ∂gaussianReal 0 1 := by
  have hpair (x y : ℝ) : ENNReal.ofReal ((f x - f y) ^ 2) ≤
      (∫⁻ s, ENNReal.ofReal (D s ^ 2) * gaussianCrossingWeight x y s) +
      ∫⁻ s, ENNReal.ofReal (D s ^ 2) * gaussianCrossingWeight y x s := by
    rcases le_total x y with hxy | hyx
    · apply le_trans _ (le_add_right le_rfl)
      rw [gaussian_crossing_square_energy D hD x y hxy (hinterval x y hxy).1,
        sub_sq_comm (f x) (f y)]
      exact ENNReal.ofReal_le_ofReal (hinterval x y hxy).2
    · apply le_trans _ (le_add_left le_rfl)
      rw [gaussian_crossing_square_energy D hD y x hyx (hinterval y x hyx).1]
      exact ENNReal.ofReal_le_ofReal (hinterval y x hyx).2
  have h := gaussian_variance_le_of_crossing_bound f hf
    (fun s => ENNReal.ofReal (D s ^ 2)) ((hD.pow_const 2).ennreal_ofReal) hpair
  rw [← ofReal_integral_eq_lintegral_ofReal hDγ (ae_of_all _ fun s => sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun s => sq_nonneg _))).mp h

end NLA.IE22
