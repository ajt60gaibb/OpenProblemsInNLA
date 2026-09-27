import NLA.FR05.SmallBall.PhaseSmallBall

/-! ## PhaseAffine -/

section

/-
The affine-cosine phase estimate used in the first branch of Lemma 3.6.

After a phase normalization, the conditional tail variance has the form
`A + B * cos φ`, where `A ≥ 1 / 4`, `0 ≤ B ≤ A`.  This module turns the
canonical estimate in `PhaseSmallBall` into the uniform bound `4t` for its
sublevel probability.  The remaining task is to connect an arbitrary phase
shift in the variance profile to this normalized form.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The one-period sublevel set for a nonnegative affine cosine profile. -/
def affineCosinePhaseSublevel (A B t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
    A + B * Real.cos φ ≤ t ^ 2}

/-- If the constant term dominates the amplitude, an affine cosine sublevel
is contained in the corresponding canonical cosine sublevel. -/
theorem affineCosinePhaseSublevel_subset_canonical
    (A B t : ℝ) (hB : 0 < B) (hBA : B ≤ A) :
    affineCosinePhaseSublevel A B t ⊆
      cosinePhaseSublevel (t / Real.sqrt B) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ A + B * Real.cos φ ≤ t ^ 2 at hφ
  constructor
  · exact hφ.1
  have hlower : B * (1 + Real.cos φ) ≤ A + B * Real.cos φ := by
    nlinarith [hBA]
  have hcanonical : B * (1 + Real.cos φ) ≤ t ^ 2 :=
    hlower.trans hφ.2
  have hdiv : 1 + Real.cos φ ≤ t ^ 2 / B := by
    apply (le_div_iff₀ hB).mpr
    simpa only [mul_comm] using hcanonical
  grw [hdiv, div_pow, Real.sq_sqrt hB.le]

/-- The canonical probability estimate at an arbitrary positive amplitude. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le
    (A B t : ℝ) (ht : 0 ≤ t) (hB : 0 < B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤
      ENNReal.ofReal (t / Real.sqrt B) := by
  grw [measure_mono (affineCosinePhaseSublevel_subset_canonical A B t hB hBA), sourceUniformInterval_cosinePhaseSublevel_le _
        (div_nonneg ht (Real.sqrt_nonneg B))]

/-- A convenient numerical form once the amplitude is bounded below. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul
    (A B t : ℝ) (ht : 0 ≤ t) (hB : 0 < B) (hBA : B ≤ A)
    (hBsmall : (1 / 16 : ℝ) ≤ B) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤ ENNReal.ofReal (4 * t) := by
  have hrootlower : (1 / 4 : ℝ) ≤ Real.sqrt B := by
    apply (Real.le_sqrt (by norm_num) hB.le).mpr
    nlinarith [hBsmall]
  have hdiv : t / Real.sqrt B ≤ 4 * t := by
    calc
      t / Real.sqrt B ≤ t / (1 / 4 : ℝ) :=
        div_le_div_of_nonneg_left ht (by norm_num) hrootlower
      _ = 4 * t := by ring
  exact (sourceUniformInterval_affineCosinePhaseSublevel_le A B t ht hB hBA).trans
    (ENNReal.ofReal_le_ofReal hdiv)

/-- In the small-amplitude regime, a sufficiently low sublevel set is empty. -/
theorem affineCosinePhaseSublevel_subset_empty
    (A B t : ℝ) (hB : 0 ≤ B) (hBhalf : B ≤ A / 2)
    (ht : t ^ 2 < A / 2) :
    affineCosinePhaseSublevel A B t ⊆ ∅ := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ A + B * Real.cos φ ≤ t ^ 2 at hφ
  have hcos : -1 ≤ Real.cos φ := Real.neg_one_le_cos φ
  have hBcos : -B ≤ B * Real.cos φ := by
    calc
      -B = B * (-1) := by ring
      _ ≤ B * Real.cos φ := mul_le_mul_of_nonneg_left hcos hB
  have hlower : A / 2 ≤ A + B * Real.cos φ := by
    nlinarith [hBhalf, hBcos]
  exfalso
  exact (not_le_of_gt ht) (hlower.trans hφ.2)

/-- The source's affine-cosine phase bound: for `A ≥ 1/4` and
`0 ≤ B ≤ A`, the sublevel probability is at most `4t`. -/
theorem sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul_of_quarter
    (A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) ≤ ENNReal.ofReal (4 * t) := by
  rcases le_total B (A / 2) with hBhalf | hhalfB
  · rcases lt_or_ge t (1 / 4 : ℝ) with htSmall | htLarge
    · have hquad : t ^ 2 < (1 / 4 : ℝ) ^ 2 := by
        have hpos : 0 < ((1 / 4 : ℝ) - t) * ((1 / 4 : ℝ) + t) :=
          mul_pos (sub_pos.mpr htSmall) (by linarith)
        nlinarith
      have hsmall : t ^ 2 < A / 2 := by
        nlinarith [hquad, hA]
      calc
        sourceUniformInterval 0 (2 * Real.pi)
            (affineCosinePhaseSublevel A B t) ≤
            sourceUniformInterval 0 (2 * Real.pi) ∅ :=
          measure_mono (affineCosinePhaseSublevel_subset_empty A B t hB hBhalf hsmall)
        _ = 0 := measure_empty
        _ ≤ ENNReal.ofReal (4 * t) := bot_le
    · let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
        isProbabilityMeasure_sourceUniformInterval (by positivity)
      calc
        sourceUniformInterval 0 (2 * Real.pi)
            (affineCosinePhaseSublevel A B t) ≤
            sourceUniformInterval 0 (2 * Real.pi) univ :=
          measure_mono (subset_univ _)
        _ = 1 := measure_univ
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (4 * t) := ENNReal.ofReal_le_ofReal (by linarith)
  · have hBsmall : (1 / 16 : ℝ) ≤ B := by
      nlinarith [hA, hhalfB]
    have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBsmall
    exact sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul
      A B t ht hBpos hBA hBsmall

end NLA.FR05

end

end

/-! ## PhaseShift -/

section

/-
Phase-shift invariance for the affine-cosine branch of Lemma 3.6.

The source variance profile is a cosine with an arbitrary phase offset.  This
module transports the interval law `sourceUniformInterval 0 (2 * π)` to the
additive circle, uses Haar invariance to remove that offset, and transports the
result back.  It therefore connects the affine estimate in `PhaseAffine` to
the source-faithful shifted profile.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

local instance phasePeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The affine cosine sublevel set on the additive phase circle. -/
def angleAffineCosineSublevel (A B t : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | A + B * Real.Angle.cos θ ≤ t ^ 2}

/-- The circular affine sublevel set after an additive phase shift. -/
def shiftedAngleAffineCosineSublevel (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | A + B * Real.Angle.cos (δ + θ) ≤ t ^ 2}

/-- The shifted affine profile written on the original real source interval. -/
def shiftedAffineCosinePhaseSublevel (δ A B t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧
    A + B * Real.cos (δ + φ) ≤ t ^ 2}

/-- Normalized Haar measure on the phase circle. -/
def phaseCircleMeasure : Measure (AddCircle (2 * Real.pi)) :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume

/-- The interval-to-circle volume identity for any measurable phase event. -/
theorem volume_phaseCircle_preimage (s : Set (AddCircle (2 * Real.pi)))
    (hs : MeasurableSet s) :
    volume s = volume (Icc 0 (2 * Real.pi) ∩ (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi))) ⁻¹' s) := by
  have h := (AddCircle.measurePreserving_mk (2 * Real.pi) 0).measure_preimage
    hs.nullMeasurableSet
  rw [zero_add, Measure.restrict_congr_set Ioc_ae_eq_Icc,
    Measure.restrict_apply (hs.preimage AddCircle.measurable_mk')] at h
  simpa only [inter_comm] using h.symm

/-- The uniform interval law transported to the normalised phase circle. -/
theorem sourceUniformInterval_phase_preimage (s : Set (AddCircle (2 * Real.pi)))
    (hs : MeasurableSet s) :
    sourceUniformInterval 0 (2 * Real.pi)
      (Icc 0 (2 * Real.pi) ∩ (fun x : ℝ ↦ (x : AddCircle (2 * Real.pi))) ⁻¹' s) =
      phaseCircleMeasure s := by
  unfold sourceUniformInterval ProbabilityTheory.cond phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc, sub_zero,
    Measure.restrict_apply (measurableSet_Icc.inter (hs.preimage AddCircle.measurable_mk')),
    inter_eq_left.mpr inter_subset_left, Measure.smul_apply, smul_eq_mul,
    volume_phaseCircle_preimage s hs]

theorem measurableSet_angleAffineCosineSublevel (A B t : ℝ) :
    MeasurableSet (angleAffineCosineSublevel A B t) := by
  unfold angleAffineCosineSublevel
  have hcos : Measurable
      (fun θ : AddCircle (2 * Real.pi) => Real.Angle.cos θ) := by
    apply Continuous.measurable
    exact Real.Angle.continuous_cos
  exact measurableSet_le
    (measurable_const.add (measurable_const.mul hcos))
    measurable_const

theorem shiftedAngleAffineCosineSublevel_eq_preimage
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    shiftedAngleAffineCosineSublevel δ A B t =
      (fun θ : AddCircle (2 * Real.pi) => δ + θ) ⁻¹'
        angleAffineCosineSublevel A B t := by
  rfl

theorem measurableSet_shiftedAngleAffineCosineSublevel
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    MeasurableSet (shiftedAngleAffineCosineSublevel δ A B t) := by
  rw [shiftedAngleAffineCosineSublevel_eq_preimage]
  exact (measurableSet_angleAffineCosineSublevel A B t).preimage
    (measurePreserving_add_left volume δ).measurable

/-- Haar invariance removes an arbitrary additive phase shift. -/
theorem volume_shiftedAngleAffineCosineSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    volume (shiftedAngleAffineCosineSublevel δ A B t) =
      volume (angleAffineCosineSublevel A B t) := by
  rw [shiftedAngleAffineCosineSublevel_eq_preimage]
  exact (measurePreserving_add_left volume δ).measure_preimage
    (measurableSet_angleAffineCosineSublevel A B t).nullMeasurableSet

theorem volume_angleAffineCosineSublevel_eq_volume_affineCosinePhaseSublevel
    (A B t : ℝ) :
    volume (angleAffineCosineSublevel A B t) =
      volume (affineCosinePhaseSublevel A B t) := by
  convert volume_phaseCircle_preimage _ (measurableSet_angleAffineCosineSublevel A B t) using 1
  congr 1

theorem measurableSet_affineCosinePhaseSublevel (A B t : ℝ) :
    MeasurableSet (affineCosinePhaseSublevel A B t) := by
  unfold affineCosinePhaseSublevel
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (measurable_const.add (measurable_const.mul Real.continuous_cos.measurable))
    measurable_const

theorem measurableSet_shiftedAffineCosinePhaseSublevel (δ A B t : ℝ) :
    MeasurableSet (shiftedAffineCosinePhaseSublevel δ A B t) := by
  unfold shiftedAffineCosinePhaseSublevel
  apply measurableSet_Icc.inter
  have hcos : Measurable (fun φ : ℝ => Real.cos (δ + φ)) := by
    fun_prop
  exact measurableSet_le (measurable_const.add (measurable_const.mul hcos))
    measurable_const

theorem sourceUniformInterval_affineCosinePhaseSublevel_eq_phaseCircleMeasure
    (A B t : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (affineCosinePhaseSublevel A B t) =
      phaseCircleMeasure (angleAffineCosineSublevel A B t) := by
  convert sourceUniformInterval_phase_preimage _
    (measurableSet_angleAffineCosineSublevel A B t) using 1
  congr 1

theorem sourceUniformInterval_shiftedAffineCosinePhaseSublevel_eq_phaseCircleMeasure
    (δ A B t : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedAffineCosinePhaseSublevel δ A B t) =
      phaseCircleMeasure
        (shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) := by
  convert sourceUniformInterval_phase_preimage _
    (measurableSet_shiftedAngleAffineCosineSublevel (δ : Real.Angle) A B t) using 1
  congr 1

theorem phaseCircleMeasure_shiftedAngleAffineCosineSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) :
    phaseCircleMeasure (shiftedAngleAffineCosineSublevel δ A B t) =
      phaseCircleMeasure (angleAffineCosineSublevel A B t) := by
  unfold phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    volume_shiftedAngleAffineCosineSublevel_eq]

theorem phaseCircleMeasure_angleAffineCosineSublevel_le_four_mul_of_quarter
    (A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    phaseCircleMeasure (angleAffineCosineSublevel A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [← sourceUniformInterval_affineCosinePhaseSublevel_eq_phaseCircleMeasure]
  exact sourceUniformInterval_affineCosinePhaseSublevel_le_four_mul_of_quarter
    A B t ht hA hB hBA

theorem phaseCircleMeasure_shiftedAngleAffineCosineSublevel_le_four_mul_of_quarter
    (δ : AddCircle (2 * Real.pi)) (A B t : ℝ) (ht : 0 ≤ t)
    (hA : (1 / 4 : ℝ) ≤ A) (hB : 0 ≤ B) (hBA : B ≤ A) :
    phaseCircleMeasure (shiftedAngleAffineCosineSublevel δ A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [phaseCircleMeasure_shiftedAngleAffineCosineSublevel_eq]
  exact phaseCircleMeasure_angleAffineCosineSublevel_le_four_mul_of_quarter
    A B t ht hA hB hBA

/-- The source-interval phase estimate with an arbitrary real phase shift. -/
theorem sourceUniformInterval_shiftedAffineCosinePhaseSublevel_le_four_mul_of_quarter
    (δ A B t : ℝ) (ht : 0 ≤ t) (hA : (1 / 4 : ℝ) ≤ A)
    (hB : 0 ≤ B) (hBA : B ≤ A) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedAffineCosinePhaseSublevel δ A B t) ≤
      ENNReal.ofReal (4 * t) := by
  rw [sourceUniformInterval_shiftedAffineCosinePhaseSublevel_eq_phaseCircleMeasure]
  exact phaseCircleMeasure_shiftedAngleAffineCosineSublevel_le_four_mul_of_quarter
    (δ : Real.Angle) A B t ht hA hB hBA

end NLA.FR05

end

end
