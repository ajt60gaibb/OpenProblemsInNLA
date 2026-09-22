import NLA.IE21.SphericalLaw
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
Gaussian density and polar decomposition for the actual IE-21 surface law.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace NLA.IE21

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f)
    {w : β → ℝ≥0∞} (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs),
    withDensity_apply _ hs, setLIntegral_map hs hw hf]
  rfl

theorem gaussian_pi_density (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  change (∫⁻ x, ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))
    ∂(Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (univ.pi s)) = _
  rw [Measure.restrict_pi_pi]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun i => (integrable_gaussianPDFReal 0 1).integrableOn))
    (Filter.Eventually.of_forall (fun x => Finset.prod_nonneg
      (fun i _ => gaussianPDFReal_nonneg 0 1 (x i))))]
  rw [integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg
      (fun x => gaussianPDFReal_nonneg 0 1 x))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num), withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal 0 1).integrableOn
    (Filter.Eventually.of_forall (fun x => gaussianPDFReal_nonneg 0 1 x))

def gaussianRadialDensity (n : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-(r ^ 2) / 2))

theorem measurable_gaussianRadialDensity (n : ℕ) : Measurable (gaussianRadialDensity n) := by
  unfold gaussianRadialDensity
  fun_prop

theorem gaussianPDF_prod (n : ℕ) (x : Fin n → ℝ) :
    ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i)) =
      gaussianRadialDensity n ‖WithLp.toLp 2 x‖ := by
  unfold gaussianRadialDensity gaussianPDFReal
  simp only [NNReal.coe_one, mul_one, sub_zero, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_sum,
    ← Finset.sum_div, ← Finset.sum_neg_distrib, EuclideanSpace.real_norm_sq_eq]

theorem stdGaussian_radial_density (n : ℕ) :
    stdGaussian (Space n) = (volume : Measure (Space n)).withDensity
      (fun g => gaussianRadialDensity n ‖g‖) := by
  rw [← map_pi_eq_stdGaussian, gaussian_pi_density]
  have heq : (fun x : Fin n → ℝ => ENNReal.ofReal (∏ i, gaussianPDFReal 0 1 (x i))) =
      (fun g : Space n => gaussianRadialDensity n ‖g‖) ∘ WithLp.toLp 2 := by
    funext x
    exact gaussianPDF_prod n x
  rw [heq, map_withDensity_comp _ (by fun_prop) (by
    exact (measurable_gaussianRadialDensity n).comp measurable_norm)]
  rw [(PiLp.volume_preserving_toLp (Fin n)).map_eq]

theorem comap_withDensity_subtype {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : Set α} (hs : MeasurableSet s) (w : α → ℝ≥0∞) :
    (μ.withDensity w).comap (Subtype.val : s → α) =
      (μ.comap (Subtype.val : s → α)).withDensity (fun x => w x) := by
  ext t ht
  rw [(MeasurableEmbedding.subtype_coe hs).comap_apply,
    withDensity_apply _ ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr ht),
    withDensity_apply _ ht]
  exact (setLIntegral_subtype hs t w).symm

def gaussianRadialMeasure (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow (n - 1)).withDensity (fun r => gaussianRadialDensity n r)

theorem gaussian_polar_product (n : ℕ) :
    ((stdGaussian (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)).map
        (homeomorphUnitSphereProd (Space n)) =
      (surfaceMeasure n).prod (gaussianRadialMeasure n) := by
  rw [stdGaussian_radial_density, comap_withDensity_subtype _
    (measurableSet_singleton _).compl]
  have heq : (fun x : ({0}ᶜ : Set (Space n)) => gaussianRadialDensity n ‖x.val‖) =
      (fun p : Sphere n × Ioi (0 : ℝ) => gaussianRadialDensity n p.2.val) ∘
        homeomorphUnitSphereProd (Space n) := by
    funext x
    simp
  rw [heq, map_withDensity_comp (w := fun p : Sphere n × Ioi (0 : ℝ) =>
      gaussianRadialDensity n p.2.val) _ (Homeomorph.measurable _)
    (by unfold gaussianRadialDensity; fun_prop),
    (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (Space n))).map_eq]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  exact (prod_withDensity_right (μ := surfaceMeasure n)
    (ν := Measure.volumeIoiPow (n - 1))
    ((measurable_gaussianRadialDensity n).comp measurable_subtype_coe)).symm

theorem gaussian_zero_mass (n : ℕ) (hn : 1 ≤ n) : (stdGaussian (Space n)) {0} = 0 := by
  let : NeZero n := ⟨by omega⟩
  rw [stdGaussian_radial_density]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton _)

theorem gaussian_polar_probability (n : ℕ) (hn : 1 ≤ n) :
    IsProbabilityMeasure ((surfaceMeasure n).prod (gaussianRadialMeasure n)) := by
  let μ := stdGaussian (Space n)
  have hfull : ∀ᵐ g ∂μ, g ∈ Set.range (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n) := by
    simp only [Subtype.range_coe]
    exact (compl_mem_ae_iff).2 (gaussian_zero_mass n hn)
  let : IsProbabilityMeasure (μ.comap (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)) :=
    (MeasurableEmbedding.subtype_coe (measurableSet_singleton _).compl).isProbabilityMeasure_comap hfull
  have hp := Measure.isProbabilityMeasure_map (μ := μ.comap
    (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n))
    (homeomorphUnitSphereProd (Space n)).measurable.aemeasurable
  rwa [gaussian_polar_product] at hp

def gaussianRadiusLaw (n : ℕ) : Measure (Ioi (0 : ℝ)) :=
  surfaceMeasure n univ • gaussianRadialMeasure n

theorem gaussian_radius_probability (n : ℕ) (hn : 1 ≤ n) :
    IsProbabilityMeasure (gaussianRadiusLaw n) := by
  let : SFinite (gaussianRadialMeasure n) := by unfold gaussianRadialMeasure; infer_instance
  let := gaussian_polar_probability n hn
  constructor
  have h := measure_univ (μ := (surfaceMeasure n).prod (gaussianRadialMeasure n))
  rw [← univ_prod_univ, Measure.prod_prod] at h
  simpa only [gaussianRadiusLaw, Measure.smul_apply, smul_eq_mul] using h

theorem gaussian_polar_normalized (n : ℕ) (hn : 1 ≤ n) :
    ((stdGaussian (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)).map
        (homeomorphUnitSphereProd (Space n)) =
      (surfaceLaw n).prod (gaussianRadiusLaw n) := by
  let : SFinite (gaussianRadialMeasure n) := by unfold gaussianRadialMeasure; infer_instance
  rw [gaussian_polar_product, surfaceLaw, gaussianRadiusLaw,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.inv_mul_cancel (surface_probability n hn).1.ne'
      (surface_probability n hn).2.1.ne, one_smul]

theorem gaussian_map_comap_nonzero (n : ℕ) (hn : 1 ≤ n) :
    ((stdGaussian (Space n)).comap
      (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)).map Subtype.val =
      stdGaussian (Space n) := by
  rw [map_comap_subtype_coe (measurableSet_singleton _).compl]
  exact Measure.restrict_eq_self_of_ae_mem ((compl_mem_ae_iff).2 (gaussian_zero_mass n hn))

theorem gaussian_ambient_polar (n : ℕ) (hn : 1 ≤ n) :
    (stdGaussian (Space n)).map (fun g => (gaussianDirection g, ‖g‖)) =
      (sphereLaw n).prod ((gaussianRadiusLaw n).map Subtype.val) := by
  let := (surface_probability n hn).2.2.1
  let := gaussian_radius_probability n hn
  let p : Sphere n × Ioi (0 : ℝ) → Space n × ℝ := Prod.map Subtype.val Subtype.val
  have hp : Measurable p := measurable_subtype_coe.prodMap measurable_subtype_coe
  have hg : Measurable (fun g : Space n => (gaussianDirection g, ‖g‖)) :=
    (measurable_gaussianDirection n).prodMk measurable_norm
  calc
    _ = (((stdGaussian (Space n)).comap
        (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)).map Subtype.val).map
          (fun g => (gaussianDirection g, ‖g‖)) := by rw [gaussian_map_comap_nonzero n hn]
    _ = (((stdGaussian (Space n)).comap
        (Subtype.val : ({0}ᶜ : Set (Space n)) → Space n)).map
          (homeomorphUnitSphereProd (Space n))).map p := by
      rw [Measure.map_map hg measurable_subtype_coe,
        Measure.map_map hp (Homeomorph.measurable _)]
      congr 1
      funext g
      apply Prod.ext <;> simp [p, gaussianDirection]
    _ = _ := by
      rw [gaussian_polar_normalized n hn]
      exact (Measure.map_prod_map (surfaceLaw n) (gaussianRadiusLaw n)
        measurable_subtype_coe measurable_subtype_coe).symm

theorem gaussian_direction_law (n : ℕ) (hn : 1 ≤ n) :
    (stdGaussian (Space n)).map gaussianDirection = sphereLaw n := by
  let := (surface_probability n hn).2.2.2.1
  let := gaussian_radius_probability n hn
  let : IsProbabilityMeasure ((gaussianRadiusLaw n).map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have h := congrArg (fun μ : Measure (Space n × ℝ) => μ.map Prod.fst)
    (gaussian_ambient_polar n hn)
  rw [Measure.map_map measurable_fst
    ((measurable_gaussianDirection n).prodMk measurable_norm),
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

theorem gaussian_norm_law (n : ℕ) (hn : 1 ≤ n) :
    (stdGaussian (Space n)).map (fun g => ‖g‖) =
      (gaussianRadiusLaw n).map Subtype.val := by
  let := (surface_probability n hn).2.2.2.1
  let := gaussian_radius_probability n hn
  let : IsProbabilityMeasure ((gaussianRadiusLaw n).map Subtype.val) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  have h := congrArg (fun μ : Measure (Space n × ℝ) => μ.map Prod.snd)
    (gaussian_ambient_polar n hn)
  rw [Measure.map_map measurable_snd
    ((measurable_gaussianDirection n).prodMk measurable_norm),
    Measure.map_snd_prod, measure_univ, one_smul] at h
  exact h

theorem gaussian_radius_direction_independent (n : ℕ) (hn : 1 ≤ n) :
    IndepFun (fun g : Space n => ‖g‖) gaussianDirection (stdGaussian (Space n)) := by
  apply IndepFun.symm
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_gaussianDirection n).aemeasurable measurable_norm.aemeasurable).2
  rw [gaussian_direction_law n hn, gaussian_norm_law n hn]
  exact gaussian_ambient_polar n hn

end NLA.IE21
