/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

The Gaussian reference construction: scale the first two coordinates by the
square root of the reference variance, leaving the other coordinates fixed.
-/
import NLA.FR05.Bridges.SourceHaarPlantedDensity
import NLA.FR05.Gaussian.ComplexVectorDensity

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace NLA.FR05


theorem sourceReferenceDensity_star (M : ℕ) (z : Signal 2) :
    sourceReferenceDensity M (star z) = sourceReferenceDensity M z := by
  simp [sourceReferenceDensity, sourceRadiusSq]

theorem sourceReference_scalar_density_product (M : ℕ) (x y : ℂ) :
    scalarGaussianDensity (sourceVariance M) 0 x *
      scalarGaussianDensity (sourceVariance M) 0 y =
      scalarComplexDensity x * scalarComplexDensity y * sourceReferenceDensity M ![x, y] := by
  unfold scalarGaussianDensity scalarComplexDensity sourceReferenceDensity sourceRadiusSq
  simp only [sub_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [_root_.mul_inv_rev, div_eq_mul_inv]
  calc
    _ = (sourceVariance M)⁻¹ ^ 2 * Real.pi⁻¹ ^ 2 *
        Real.exp (-(Complex.normSq x + Complex.normSq y) * (sourceVariance M)⁻¹) := by
      rw [show -(Complex.normSq x + Complex.normSq y) * (sourceVariance M)⁻¹ =
        -Complex.normSq x * (sourceVariance M)⁻¹ + -Complex.normSq y * (sourceVariance M)⁻¹ by ring,
        Real.exp_add]
      ring
    _ = _ := by
      rw [show -(Complex.normSq x + Complex.normSq y) * (sourceVariance M)⁻¹ =
        -Complex.normSq x + -Complex.normSq y +
          (-((sourceVariance M)⁻¹ - 1) * (Complex.normSq x + Complex.normSq y)) by ring,
        Real.exp_add, Real.exp_add]
      ring

/-- The literal reference density is the law of a Gaussian head scaled by
the square root of its covariance parameter. -/
theorem sourceReferenceLaw_eq_map_scale (M : ℕ) :
    sourceReferenceLaw M = (standardComplexGaussianTail 2).map
      (fun z ↦ Real.sqrt (sourceVariance M) • z) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [sourceReferenceLaw, lintegral_withDensity_eq_lintegral_mul _
      (measurable_sourceReferenceDensity M).ennreal_ofReal hf,
    lintegral_standardComplexGaussianTail_two _
      ((measurable_sourceReferenceDensity M).ennreal_ofReal.mul hf),
    lintegral_map hf (by fun_prop)]
  have htri (z : Signal 2) : Real.sqrt (sourceVariance M) • z =
      triangularGaussian (sourceVariance M) (sourceVariance M) 0 0 z := by
    ext i
    fin_cases i <;> simp [triangularGaussian]
  simp_rw [htri]
  rw [← lintegral_triangularGaussian (sourceVariance_pos M) (sourceVariance_pos M) 0 0 f hf]
  apply lintegral_congr
  intro x
  apply lintegral_congr
  intro y
  simp only [Pi.mul_apply, triangularGaussianDensity, Pi.zero_apply, zero_mul,
    add_zero, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    sourceReference_scalar_density_product,
    ENNReal.ofReal_mul (scalarComplexDensity_nonneg x),
    ENNReal.ofReal_mul (scalarComplexDensity_nonneg y), mul_assoc]

/-- The nonzero diagonal entries of the reference deformation. -/
def sourceReferenceScale (M n : ℕ) (j : Fin (n + 2)) : ℂ :=
  if j.val < 2 then (Real.sqrt (sourceVariance M) : ℂ) else 1

theorem sourceReferenceScale_ne_zero (M n : ℕ) (j : Fin (n + 2)) :
    sourceReferenceScale M n j ≠ 0 := by
  unfold sourceReferenceScale
  split_ifs
  · exact_mod_cast (Real.sqrt_pos.mpr (sourceVariance_pos M)).ne'
  · exact one_ne_zero

def sourceReferenceColumn (M : ℕ) {n : ℕ} (x : Signal (n + 2)) : Signal (n + 2) :=
  fun j ↦ sourceReferenceScale M n j * x j

@[fun_prop] theorem measurable_sourceReferenceColumn (M n : ℕ) :
    Measurable (sourceReferenceColumn M (n := n)) := by
  unfold sourceReferenceColumn
  fun_prop

theorem sourceReferenceColumn_join (M : ℕ) {n : ℕ} (p : Signal 2 × Signal n) :
    sourceReferenceColumn M (sourceHeadTailJoin p) =
      sourceHeadTailJoin (Real.sqrt (sourceVariance M) • p.1, p.2) := by
  ext j
  by_cases h0 : j.val = 0
  · simp [sourceReferenceColumn, sourceReferenceScale, sourceHeadTailJoin, joinTwo, h0,
      Complex.real_smul]
  by_cases h1 : j.val = 1
  · simp [sourceReferenceColumn, sourceReferenceScale, sourceHeadTailJoin, joinTwo, h1,
      Complex.real_smul]
  · have hj : ¬ j.val < 2 := by lia
    simp [sourceReferenceColumn, sourceReferenceScale, sourceHeadTailJoin, joinTwo, h0, h1, hj]

theorem standardComplexGaussianTail_map_referenceColumn (M n : ℕ) :
    (standardComplexGaussianTail (n + 2)).map (sourceReferenceColumn M) =
      (standardComplexGaussianTail (n + 2)).withDensity
        (fun x ↦ ENNReal.ofReal (sourceReferenceDensity M (sourceHead x))) := by
  rw [← standardComplexGaussianTail_prod_map_sourceHeadTailJoin n,
    Measure.map_map (measurable_sourceReferenceColumn M n) measurable_sourceHeadTailJoin]
  have he : sourceReferenceColumn M ∘ (sourceHeadTailJoin (n := n)) =
      sourceHeadTailJoin ∘ Prod.map (fun z ↦ Real.sqrt (sourceVariance M) • z) id :=
    funext (sourceReferenceColumn_join M)
  rw [he, ← Measure.map_map measurable_sourceHeadTailJoin (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) measurable_id, Measure.map_id,
    ← sourceReferenceLaw_eq_map_scale, sourceReferenceLaw,
    prod_withDensity_left (measurable_sourceReferenceDensity M).ennreal_ofReal]
  have hd : (fun p : Signal 2 × Signal n ↦ ENNReal.ofReal (sourceReferenceDensity M p.1)) =
      fun p ↦ ENNReal.ofReal (sourceReferenceDensity M (sourceHead (sourceHeadTailJoin p))) := by
    simp only [sourceHead_sourceHeadTailJoin]
  rw [hd, map_withDensity_comp _ _ measurable_sourceHeadTailJoin
    (fun x ↦ ENNReal.ofReal (sourceReferenceDensity M (sourceHead x)))
    (((measurable_sourceReferenceDensity M).comp measurable_sourceHead).ennreal_ofReal)]

def sourceReferenceFrame (M : ℕ) {m n : ℕ} (A : Frame m (n + 2)) : Frame m (n + 2) :=
  fun i ↦ sourceReferenceColumn M (A i)

@[fun_prop] theorem measurable_sourceReferenceFrame (M m n : ℕ) :
    Measurable (sourceReferenceFrame M (m := m) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_sourceReferenceColumn M n).comp (measurable_pi_apply i)

/-- The reference frame is obtained by an invertible diagonal change of
coordinates, which preserves the original all-signals injectivity predicate. -/
theorem phaseRetrievalInjective_referenceFrame (M : ℕ) {m n : ℕ}
    (A : Frame m (n + 2)) :
    PhaseRetrievalInjective (sourceReferenceFrame M A) ↔ PhaseRetrievalInjective A := by
  have he : sourceReferenceFrame M A = A * Matrix.diagonal (sourceReferenceScale M n) := by
    ext i j
    simp [sourceReferenceFrame, sourceReferenceColumn, Matrix.mul_diagonal, mul_comm]
  rw [he]
  exact phaseRetrievalInjective_mul_diagonal A _ (sourceReferenceScale_ne_zero M n)

/-- The canonical reference frame law before Haar orientation. -/
def sourceReferenceFrameLaw (M m n : ℕ) : Measure (Frame m (n + 2)) :=
  (standardComplexGaussianFrame m (n + 2)).map (sourceReferenceFrame M)

instance (M m n : ℕ) : IsProbabilityMeasure (sourceReferenceFrameLaw M m n) :=
  Measure.isProbabilityMeasure_map (measurable_sourceReferenceFrame M m n).aemeasurable

theorem sourceReferenceFrameLaw_eq_withDensity {M m n : ℕ} (hM : 2 ≤ M) :
    sourceReferenceFrameLaw M m n =
      (standardComplexGaussianFrame m (n + 2)).withDensity
        (fun A ↦ ENNReal.ofReal (∏ i, sourceReferenceDensity M (sourceHead (star (A i))))) := by
  let f : Signal (n + 2) → ℝ := fun x ↦ sourceReferenceDensity M (sourceHead (star x))
  have hf : Measurable f := (measurable_sourceReferenceDensity M).comp
    (measurable_sourceHead.comp (by fun_prop))
  have hf0 : ∀ x, 0 ≤ f x := fun x ↦ (sourceReferenceDensity_pos M _).le
  have hfi : Integrable f (standardComplexGaussianTail (n + 2)) := by
    apply Integrable.of_bound hf.aestronglyMeasurable 4
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    exact sourceReferenceDensity_le_four hM _
  have hrow : (standardComplexGaussianTail (n + 2)).map (sourceReferenceColumn M) =
      (standardComplexGaussianTail (n + 2)).withDensity (fun x ↦ ENNReal.ofReal (f x)) := by
    rw [standardComplexGaussianTail_map_referenceColumn]
    congr 1
    funext x
    exact congrArg ENNReal.ofReal (sourceReferenceDensity_star M (sourceHead x)).symm
  have : IsProbabilityMeasure ((standardComplexGaussianTail (n + 2)).withDensity
      (fun x ↦ ENNReal.ofReal (f x))) := by
    rw [← hrow]
    exact Measure.isProbabilityMeasure_map (measurable_sourceReferenceColumn M n).aemeasurable
  unfold sourceReferenceFrameLaw
  rw [standardComplexGaussianFrame_eq_pi]
  have hpi := Measure.pi_map_pi (μ := fun _ : Fin m ↦ standardComplexGaussianTail (n + 2))
    (f := fun _ : Fin m ↦ sourceReferenceColumn M (n := n))
    (fun _ ↦ (measurable_sourceReferenceColumn M n).aemeasurable)
  change Measure.map (fun A : Fin m → Signal (n + 2) ↦ fun i ↦ sourceReferenceColumn M (A i)) _ = _
  rw [hpi]
  simp_rw [hrow]
  exact Measure.pi_withDensity_ofReal (ι := Fin m) _ f hf0 hfi

end NLA.FR05
