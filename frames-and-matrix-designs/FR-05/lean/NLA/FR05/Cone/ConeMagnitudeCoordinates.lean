import NLA.FR05.Gaussian.GaussianPolarLaw

set_option autoImplicit false
noncomputable section
open MeasureTheory Real Matrix Set
open scoped ENNReal

namespace NLA.FR05

def coneMagnitudeMap (p : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![p 0 * (1 + p 1) / 2, p 0 * (1 - p 1) / 2]

def coneMagnitudeInverse (u : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![u 0 + u 1, (u 0 - u 1) / (u 0 + u 1)]

def coneMagnitudeDerivative (p : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  (Matrix.toLin' !![(1 + p 1) / 2, p 0 / 2; (1 - p 1) / 2, -p 0 / 2]).toContinuousLinearMap

@[fun_prop]
theorem continuous_coneMagnitudeMap : Continuous coneMagnitudeMap := by
  unfold coneMagnitudeMap
  fun_prop

theorem hasFDerivAt_coneMagnitudeMap (p : Fin 2 → ℝ) :
    HasFDerivAt coneMagnitudeMap (coneMagnitudeDerivative p) p := by
  have h0 := (((hasFDerivAt_apply (𝕜 := ℝ) 0 p).mul
    ((hasFDerivAt_const (1 : ℝ) p).add (hasFDerivAt_apply 1 p))).const_mul (1 / 2 : ℝ))
  have h1 := (((hasFDerivAt_apply (𝕜 := ℝ) 0 p).mul
    ((hasFDerivAt_const (1 : ℝ) p).sub (hasFDerivAt_apply 1 p))).const_mul (1 / 2 : ℝ))
  let d0 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (p 0 • (0 + ContinuousLinearMap.proj 1) + (1 + p 1) • ContinuousLinearMap.proj 0)
  let d1 : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (p 0 • (0 - ContinuousLinearMap.proj 1) + (1 - p 1) • ContinuousLinearMap.proj 0)
  have h : ∀ i : Fin 2, HasFDerivAt
      (![fun x : Fin 2 → ℝ ↦ (1 / 2 : ℝ) * (x 0 * (1 + x 1)),
          fun x : Fin 2 → ℝ ↦ (1 / 2 : ℝ) * (x 0 * (1 - x 1))] i)
      (![d0, d1] i) p := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
  convert! hasFDerivAt_pi.mpr h using 1
  · funext x i
    fin_cases i <;> simp [coneMagnitudeMap] <;> ring
  · ext x i
    fin_cases i <;>
      simp [d0, d1, coneMagnitudeDerivative, Matrix.toLin'_apply, Matrix.mulVec,
        dotProduct, Fin.sum_univ_two] <;> ring

theorem coneMagnitudeDerivative_det (p : Fin 2 → ℝ) :
    (coneMagnitudeDerivative p).det = -p 0 / 2 := by
  simp only [coneMagnitudeDerivative, ContinuousLinearMap.det,
    LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin', Matrix.det_fin_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  ring

theorem coneMagnitudeInverse_map {p : Fin 2 → ℝ} (hp : p 0 ≠ 0) :
    coneMagnitudeInverse (coneMagnitudeMap p) = p := by
  ext i
  fin_cases i
  · simp [coneMagnitudeInverse, coneMagnitudeMap]
    ring
  · simp only [coneMagnitudeInverse, coneMagnitudeMap, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have he : p 0 * (1 + p 1) / 2 + p 0 * (1 - p 1) / 2 = p 0 := by ring
    rw [he]
    field_simp
    simp

theorem coneMagnitudeMap_inverse {u : Fin 2 → ℝ} (hu : u 0 + u 1 ≠ 0) :
    coneMagnitudeMap (coneMagnitudeInverse u) = u := by
  ext i
  fin_cases i <;> simp [coneMagnitudeMap, coneMagnitudeInverse] <;> field_simp [hu] <;> ring

def coneMagnitudeDomain (δ ε : ℝ) : Set (Fin 2 → ℝ) :=
  {p | δ ≤ p 0 ∧ |p 1| ≤ ε}

def coneMagnitudeRegion (δ ε : ℝ) : Set (Fin 2 → ℝ) :=
  {u | δ ≤ u 0 + u 1 ∧ |(u 0 - u 1) / (u 0 + u 1)| ≤ ε}

theorem measurableSet_coneMagnitudeDomain (δ ε : ℝ) : MeasurableSet (coneMagnitudeDomain δ ε) := by
  unfold coneMagnitudeDomain
  exact (measurableSet_le measurable_const (measurable_pi_apply 0)).inter
    (measurableSet_le (measurable_pi_apply 1).abs measurable_const)

theorem coneMagnitudeMap_injOn {δ ε : ℝ} (hδ : 0 < δ) :
    InjOn coneMagnitudeMap (coneMagnitudeDomain δ ε) := by
  intro p hp q hq he
  have h := congrArg coneMagnitudeInverse he
  rw [coneMagnitudeInverse_map (ne_of_gt (hδ.trans_le hp.1)),
    coneMagnitudeInverse_map (ne_of_gt (hδ.trans_le hq.1))] at h
  exact h

theorem coneMagnitudeMap_image {δ ε : ℝ} (hδ : 0 < δ) :
    coneMagnitudeMap '' coneMagnitudeDomain δ ε = coneMagnitudeRegion δ ε := by
  ext u
  constructor
  · rintro ⟨p, hp, rfl⟩
    have h := coneMagnitudeInverse_map (ne_of_gt (hδ.trans_le hp.1))
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change coneMagnitudeMap p 0 + coneMagnitudeMap p 1 = p 0 at h0
    change (coneMagnitudeMap p 0 - coneMagnitudeMap p 1) /
      (coneMagnitudeMap p 0 + coneMagnitudeMap p 1) = p 1 at h1
    change δ ≤ coneMagnitudeMap p 0 + coneMagnitudeMap p 1 ∧
      |(coneMagnitudeMap p 0 - coneMagnitudeMap p 1) /
        (coneMagnitudeMap p 0 + coneMagnitudeMap p 1)| ≤ ε
    rw [h1, h0]
    exact hp
  · intro hu
    refine ⟨coneMagnitudeInverse u, ?_, coneMagnitudeMap_inverse (ne_of_gt (hδ.trans_le hu.1))⟩
    exact hu

theorem coneMagnitudeMap_volume {δ ε : ℝ} (hδ : 0 < δ) :
    ((volume.restrict (coneMagnitudeDomain δ ε)).withDensity
      (fun p ↦ ENNReal.ofReal (p 0 / 2))).map coneMagnitudeMap =
      volume.restrict (coneMagnitudeRegion δ ε) := by
  have h := map_withDensity_abs_det_fderiv_eq_addHaar
    (volume : Measure (Fin 2 → ℝ)) (measurableSet_coneMagnitudeDomain δ ε).nullMeasurableSet
    (fun p _ ↦ (hasFDerivAt_coneMagnitudeMap p).hasFDerivWithinAt)
    (coneMagnitudeMap_injOn hδ)
  rw [coneMagnitudeMap_image hδ] at h
  rw [← h]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_coneMagnitudeDomain δ ε)] with p hp
  rw [coneMagnitudeDerivative_det, neg_div, abs_neg,
    abs_of_nonneg (div_nonneg (hδ.trans_le hp.1).le (by norm_num))]


theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (d : β → ℝ≥0∞) (hd : Measurable d) :
    (μ.withDensity (fun x ↦ d (f x))).map f = (μ.map f).withDensity d := by
  apply Measure.ext_of_lintegral
  intro g hg
  calc
    _ = ∫⁻ x, g (f x) ∂μ.withDensity (fun x ↦ d (f x)) := lintegral_map hg hf
    _ = ∫⁻ x, d (f x) * g (f x) ∂μ :=
      lintegral_withDensity_eq_lintegral_mul μ (hd.comp hf) (hg.comp hf)
    _ = ∫⁻ y, (d * g) y ∂μ.map f := (lintegral_map (hd.mul hg) hf).symm
    _ = _ := (lintegral_withDensity_eq_lintegral_mul (μ.map f) hd hg).symm


theorem coneMagnitudeMap_withDensity {δ ε : ℝ} (hδ : 0 < δ)
    (d : (Fin 2 → ℝ) → ℝ≥0∞) (hd : Measurable d) :
    ((volume.restrict (coneMagnitudeDomain δ ε)).withDensity
      (fun p ↦ ENNReal.ofReal (p 0 / 2) * d (coneMagnitudeMap p))).map coneMagnitudeMap =
      (volume.restrict (coneMagnitudeRegion δ ε)).withDensity d := by
  have hj : Measurable (fun p : Fin 2 → ℝ ↦ ENNReal.ofReal (p 0 / 2)) := by fun_prop
  have he : (volume.restrict (coneMagnitudeDomain δ ε)).withDensity
      (fun p ↦ ENNReal.ofReal (p 0 / 2) * d (coneMagnitudeMap p)) =
      ((volume.restrict (coneMagnitudeDomain δ ε)).withDensity
        (fun p ↦ ENNReal.ofReal (p 0 / 2))).withDensity (fun p ↦ d (coneMagnitudeMap p)) :=
    withDensity_mul _ hj (hd.comp continuous_coneMagnitudeMap.measurable)
  rw [he]
  rw [map_withDensity_comp _ _ continuous_coneMagnitudeMap.measurable d hd,
    coneMagnitudeMap_volume hδ]

theorem coneMagnitudeRegion_nonneg {δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ 1)
    {u : Fin 2 → ℝ} (hu : u ∈ coneMagnitudeRegion δ ε) :
    0 ≤ u 0 ∧ 0 ≤ u 1 := by
  have hs := hδ.trans_le hu.1
  have hb : |u 0 - u 1| ≤ u 0 + u 1 := by
    have h := hu.2.trans hε
    rw [abs_div, abs_of_pos hs, div_le_one hs] at h
    exact h
  have h := abs_le.mp hb
  constructor <;> linarith

end NLA.FR05
