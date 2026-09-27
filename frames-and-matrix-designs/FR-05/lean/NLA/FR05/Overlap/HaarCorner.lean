import NLA.FR05.Overlap.Overlap

/-!
# The overlap law as a corner of a Haar unitary

The relative position of two independent Haar unitaries is Haar. Applying the
corner map identifies the overlap law; the proof uses mathlib's measure-preserving
group shear rather than a separate integral-extensionality argument.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

namespace NLA.FR05

/-- Normalised Haar measure on the compact unitary group is also right invariant. -/
instance (n : ℕ) : (sourceUnitaryLaw n).IsMulRightInvariant where
  map_mul_right_eq_self U := by
    let : IsProbabilityMeasure ((sourceUnitaryLaw n).map (· * U)) :=
      Measure.isProbabilityMeasure_map (measurable_mul_const U).aemeasurable
    exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

/-- The leading two-by-two corner of a unitary matrix. -/
def sourceHaarCorner {M : ℕ} (hM : 2 ≤ M) (U : SourceUnitary M) :
    SourceOverlapMatrix :=
  fun i j ↦ U.val (Fin.castLE hM i) (Fin.castLE hM j)

/-- Taking the leading corner is continuous. -/
@[fun_prop]
theorem continuous_sourceHaarCorner {M : ℕ} (hM : 2 ≤ M) :
    Continuous (sourceHaarCorner hM) := by
  exact continuous_pi fun i ↦ continuous_pi fun j ↦
    (continuous_apply (Fin.castLE hM j)).comp
      ((continuous_apply (Fin.castLE hM i)).comp continuous_subtype_val)

/-- A two-frame overlap is the leading corner of the relative unitary. -/
theorem sourceOverlap_eq_corner {M : ℕ} (hM : 2 ≤ M) (U V : SourceUnitary M) :
    sourceOverlap hM U V = sourceHaarCorner hM (star U * V) := by
  ext i j
  simp [sourceOverlap, sourceTwoFrame, sourceHaarCorner, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.star_eq_conjTranspose]

/-- The overlap of independent Haar frames has the Haar-corner law. -/
theorem sourceOverlapLaw_eq_haarCorner {M : ℕ} (hM : 2 ≤ M) :
    sourceOverlapLaw M hM = (sourceUnitaryLaw M).map (sourceHaarCorner hM) := by
  let μ := sourceUnitaryLaw M
  have hprod : MeasurePreserving (fun p : SourceUnitary M × SourceUnitary M ↦
      p.1⁻¹ * p.2) (μ.prod μ) μ :=
    measurePreserving_snd.comp (measurePreserving_prod_inv_mul μ μ)
  have he : (fun p : SourceUnitary M × SourceUnitary M ↦ sourceOverlap hM p.1 p.2) =
      sourceHaarCorner hM ∘ (fun p ↦ p.1⁻¹ * p.2) := by
    funext p
    exact sourceOverlap_eq_corner hM p.1 p.2
  rw [sourceOverlapLaw, he, ← Measure.map_map
    (continuous_sourceHaarCorner hM).measurable hprod.measurable, hprod.map_eq]

end NLA.FR05
