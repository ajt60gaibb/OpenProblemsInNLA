/-
The absolute affine-trigonometric phase branch in Lemma 3.6.

The inverse-cosine square-root modulus controls arbitrary cosine bands.
Its constant extension outside `[-1, 1]` avoids separate band-clamping
definitions; the affine reduction uses the cosine addition formula.
-/
import NLA.FR05.SmallBall.PhaseAffine

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace NLA.FR05

local instance phasePeriodPositiveAbsolute : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- On `[-1, 1]`, the inverse-cosine gap has a square-root modulus.
This is sharp at either endpoint. -/
theorem arccos_gap_sq_le (x y : ℝ)
    (hy : -1 ≤ y) (hx : x ≤ 1) (hyx : y ≤ x) :
    (Real.arccos y - Real.arccos x) ^ 2 ≤
      (Real.pi ^ 2 / 2) * (x - y) := by
  let α := Real.arccos x
  let β := Real.arccos y
  have hα0 : 0 ≤ α := Real.arccos_nonneg x
  have hβpi : β ≤ Real.pi := Real.arccos_le_pi y
  have hαβ : α ≤ β := Real.arccos_le_arccos hyx
  have hs : Real.sin ((β - α) / 2) ≤ Real.sin ((α + β) / 2) := by
    have h := strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc
      (x := (β - α) / 2) (y := Real.pi - (β - α) / 2) (z := (α + β) / 2)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      ⟨by linarith, by linarith⟩
    simpa only [Real.sin_pi_sub, min_self] using h
  have hd := Real.cos_le_one_sub_mul_cos_sq
    (show |β - α| ≤ Real.pi from abs_le.mpr ⟨by linarith, by linarith⟩)
  have hdiff : Real.cos α - Real.cos β =
      2 * Real.sin ((α + β) / 2) * Real.sin ((β - α) / 2) := by
    rw [Real.cos_sub_cos, show (α - β) / 2 = -((β - α) / 2) by ring, Real.sin_neg]
    ring
  have hhalf := Real.cos_two_mul ((β - α) / 2)
  rw [show 2 * ((β - α) / 2) = β - α by ring] at hhalf
  have hsquare := Real.sin_sq_add_cos_sq ((β - α) / 2)
  have hnonneg := mul_nonneg (sub_nonneg.mpr hs)
    (Real.sin_nonneg_of_nonneg_of_le_pi (x := (β - α) / 2) (by linarith) (by linarith))
  have hxy : Real.cos α - Real.cos β = x - y := by
    rw [Real.cos_arccos (hy.trans hyx) hx, Real.cos_arccos hy (hyx.trans hx)]
  have hgap : 1 - Real.cos (β - α) ≤ x - y := by nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hd (sq_nonneg Real.pi)
  field_simp at hscaled
  change (β - α) ^ 2 ≤ _
  nlinarith [mul_le_mul_of_nonneg_left hgap (sq_nonneg Real.pi)]

/-- The inverse-cosine modulus holds on the whole real line: projecting onto
`[-1, 1]` does not change arccosine or increase the width. -/
theorem arccos_gap_le_pi_sqrt (x y h : ℝ)
    (hyx : y ≤ x) (hh : 0 ≤ h) (hwidth : x - y ≤ 2 * h) :
    Real.arccos y - Real.arccos x ≤ Real.pi * Real.sqrt h := by
  let p := Set.projIcc (-1 : ℝ) 1 (by norm_num)
  have hp (z : ℝ) : Real.arccos (p z) = Real.arccos z := by
    simp only [p, Set.coe_projIcc, Real.antitone_arccos.map_max, Real.antitone_arccos.map_min,
      Real.arccos_neg_one, Real.arccos_one, max_eq_right (Real.arccos_nonneg z),
      min_eq_right (Real.arccos_le_pi z)]
  have hmono : Monotone (fun z ↦ (p z : ℝ)) := by
    intro a b hab
    exact max_le_max_left _ (min_le_min_left _ hab)
  have hw : (p x : ℝ) - p y ≤ 2 * h := by
    have h := Set.abs_projIcc_sub_projIcc (a := (-1 : ℝ)) (b := 1)
      (c := x) (d := y) (by norm_num)
    rw [abs_of_nonneg (sub_nonneg.mpr (hmono hyx)),
      abs_of_nonneg (sub_nonneg.mpr hyx)] at h
    exact h.trans hwidth
  have hgap := arccos_gap_sq_le (p x) (p y) (p y).2.1 (p x).2.2 (hmono hyx)
  rw [hp, hp] at hgap
  have hwidth' := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ Real.pi ^ 2 / 2)
  apply le_of_sq_le_sq _ (by positivity : 0 ≤ Real.pi * Real.sqrt h)
  rw [mul_pow, Real.sq_sqrt hh]
  linarith

/-- The one-period sublevel set of a cosine at an arbitrary level. -/
def cosineBandPhaseSublevel (q h : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos φ - q| ≤ h}

/-- A cosine band on one period has at most two monotone pieces. -/
theorem cosineBandPhaseSublevel_subset_twoIntervals (q h : ℝ) :
    cosineBandPhaseSublevel q h ⊆
      Icc (Real.arccos (q + h))
          (Real.arccos (q - h)) ∪
        Icc (2 * Real.pi - Real.arccos (q - h))
          (2 * Real.pi - Real.arccos (q + h)) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos φ - q| ≤ h at hφ
  obtain ⟨hlo, hhi⟩ := abs_le.mp hφ.2
  have hα := Real.arccos_le_arccos (show Real.cos φ ≤ q + h by linarith)
  have hβ := Real.arccos_le_arccos (show q - h ≤ Real.cos φ by linarith)
  rcases le_total φ Real.pi with hleft | hright
  · rw [Real.arccos_cos hφ.1.1 hleft] at hα hβ
    exact Or.inl ⟨hα, hβ⟩
  · have hreflect : Real.arccos (Real.cos φ) = 2 * Real.pi - φ := by
      rw [← Real.cos_two_pi_sub φ,
        Real.arccos_cos (by linarith [hφ.1.2]) (by linarith)]
    rw [hreflect] at hα hβ
    exact Or.inr ⟨by linarith, by linarith⟩

/-- Raw Lebesgue estimate for a cosine band.  The square-root dependence is
sharp when the level is tangent to the cosine at an endpoint. -/
theorem volume_cosineBandPhaseSublevel_le (q h : ℝ) (hh : 0 ≤ h) :
    volume (cosineBandPhaseSublevel q h) ≤
      ENNReal.ofReal (2 * Real.pi * Real.sqrt h) := by
  let lo : ℝ := q - h
  let hi : ℝ := q + h
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; linarith
  have hgap : Real.arccos lo - Real.arccos hi ≤ Real.pi * Real.sqrt h :=
    arccos_gap_le_pi_sqrt hi lo h hlohi hh (by dsimp [lo, hi]; linarith)
  have hd0 : 0 ≤ Real.arccos lo - Real.arccos hi :=
    sub_nonneg.mpr (Real.arccos_le_arccos hlohi)
  let I₁ : Set ℝ := Icc (Real.arccos hi) (Real.arccos lo)
  let I₂ : Set ℝ := Icc (2 * Real.pi - Real.arccos lo)
    (2 * Real.pi - Real.arccos hi)
  have hsubset : cosineBandPhaseSublevel q h ⊆ I₁ ∪ I₂ := by
    simpa only [I₁, I₂, lo, hi] using
      cosineBandPhaseSublevel_subset_twoIntervals q h
  calc
    volume (cosineBandPhaseSublevel q h) ≤ volume (I₁ ∪ I₂) :=
      measure_mono hsubset
    _ ≤ volume I₁ + volume I₂ := measure_union_le I₁ I₂
    _ = ENNReal.ofReal (Real.arccos lo - Real.arccos hi) +
          ENNReal.ofReal (Real.arccos lo - Real.arccos hi) := by
      rw [Real.volume_Icc, Real.volume_Icc]
      have hI₂ : 2 * Real.pi - Real.arccos hi -
          (2 * Real.pi - Real.arccos lo) =
          Real.arccos lo - Real.arccos hi := by ring
      rw [hI₂]
    _ = ENNReal.ofReal ((Real.arccos lo - Real.arccos hi) +
          (Real.arccos lo - Real.arccos hi)) := by
      rw [ENNReal.ofReal_add hd0 hd0]
    _ ≤ ENNReal.ofReal ((Real.pi * Real.sqrt h) +
          (Real.pi * Real.sqrt h)) := by
      apply ENNReal.ofReal_le_ofReal
      linarith
    _ = ENNReal.ofReal (2 * Real.pi * Real.sqrt h) := by
      congr 1
      ring

theorem measurableSet_cosineBandPhaseSublevel (q h : ℝ) :
    MeasurableSet (cosineBandPhaseSublevel q h) := by
  unfold cosineBandPhaseSublevel
  apply measurableSet_Icc.inter
  exact measurableSet_le
    ((Real.continuous_cos.measurable.sub measurable_const).abs)
    measurable_const

/-- The source's uniform phase law assigns a cosine band probability at most
the square root of its width. -/
theorem sourceUniformInterval_cosineBandPhaseSublevel_le_sqrt
    (q h : ℝ) (hh : 0 ≤ h) :
    sourceUniformInterval 0 (2 * Real.pi) (cosineBandPhaseSublevel q h) ≤
      ENNReal.ofReal (Real.sqrt h) := by
  have hsub : cosineBandPhaseSublevel q h ⊆ Icc 0 (2 * Real.pi) := by
    intro φ hφ
    exact hφ.1
  have hvol := volume_cosineBandPhaseSublevel_le q h hh
  have hpi : 0 < 2 * Real.pi := by positivity
  have hpi0 : ENNReal.ofReal (2 * Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hpi).ne'
  unfold sourceUniformInterval ProbabilityTheory.cond
  rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc,
    Measure.restrict_apply (measurableSet_cosineBandPhaseSublevel q h),
    Set.inter_eq_left.mpr hsub]
  simp only [sub_zero]
  calc
    (ENNReal.ofReal (2 * Real.pi))⁻¹ * volume (cosineBandPhaseSublevel q h) ≤
        (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ENNReal.ofReal (2 * Real.pi * Real.sqrt h) :=
      mul_le_mul_of_nonneg_left hvol bot_le
    _ = ENNReal.ofReal (Real.sqrt h) := by
      rw [ENNReal.ofReal_mul hpi.le, ← mul_assoc,
        ENNReal.inv_mul_cancel hpi0 ENNReal.ofReal_ne_top, one_mul]

/-- The cosine band written on the additive phase circle. -/
def angleCosineBandPhaseSublevel (q h : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | |Real.Angle.cos θ - q| ≤ h}

/-- The same band after a phase translation. -/
def shiftedAngleCosineBandPhaseSublevel
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) : Set (AddCircle (2 * Real.pi)) :=
  {θ : AddCircle (2 * Real.pi) | |Real.Angle.cos (δ + θ) - q| ≤ h}

/-- The shifted band on the source interval. -/
def shiftedCosineBandPhaseSublevel (δ q h : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |Real.cos (δ + φ) - q| ≤ h}

theorem measurableSet_angleCosineBandPhaseSublevel (q h : ℝ) :
    MeasurableSet (angleCosineBandPhaseSublevel q h) := by
  unfold angleCosineBandPhaseSublevel
  have hcos : Measurable
      (fun θ : AddCircle (2 * Real.pi) => Real.Angle.cos θ) := by
    apply Continuous.measurable
    exact Real.Angle.continuous_cos
  exact measurableSet_le (hcos.sub measurable_const).abs measurable_const

theorem shiftedAngleCosineBandPhaseSublevel_eq_preimage
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    shiftedAngleCosineBandPhaseSublevel δ q h =
      (fun θ : AddCircle (2 * Real.pi) => δ + θ) ⁻¹'
        angleCosineBandPhaseSublevel q h := by
  rfl

theorem measurableSet_shiftedAngleCosineBandPhaseSublevel
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    MeasurableSet (shiftedAngleCosineBandPhaseSublevel δ q h) := by
  rw [shiftedAngleCosineBandPhaseSublevel_eq_preimage]
  exact (measurableSet_angleCosineBandPhaseSublevel q h).preimage
    (measurePreserving_add_left volume δ).measurable

theorem volume_shiftedAngleCosineBandPhaseSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    volume (shiftedAngleCosineBandPhaseSublevel δ q h) =
      volume (angleCosineBandPhaseSublevel q h) := by
  rw [shiftedAngleCosineBandPhaseSublevel_eq_preimage]
  exact (measurePreserving_add_left volume δ).measure_preimage
    (measurableSet_angleCosineBandPhaseSublevel q h).nullMeasurableSet

theorem measurableSet_shiftedCosineBandPhaseSublevel (δ q h : ℝ) :
    MeasurableSet (shiftedCosineBandPhaseSublevel δ q h) := by
  unfold shiftedCosineBandPhaseSublevel
  apply measurableSet_Icc.inter
  have hcos : Measurable (fun φ : ℝ => Real.cos (δ + φ)) := by fun_prop
  exact measurableSet_le (hcos.sub measurable_const).abs measurable_const

theorem volume_angleCosineBandPhaseSublevel_eq_volume_cosineBandPhaseSublevel
    (q h : ℝ) :
    volume (angleCosineBandPhaseSublevel q h) =
      volume (cosineBandPhaseSublevel q h) := by
  convert volume_phaseCircle_preimage _ (measurableSet_angleCosineBandPhaseSublevel q h) using 1
  congr 1

theorem sourceUniformInterval_cosineBandPhaseSublevel_eq_phaseCircleMeasure
    (q h : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi) (cosineBandPhaseSublevel q h) =
      phaseCircleMeasure (angleCosineBandPhaseSublevel q h) := by
  convert sourceUniformInterval_phase_preimage _
    (measurableSet_angleCosineBandPhaseSublevel q h) using 1
  congr 1

theorem sourceUniformInterval_shiftedCosineBandPhaseSublevel_eq_phaseCircleMeasure
    (δ q h : ℝ) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedCosineBandPhaseSublevel δ q h) =
      phaseCircleMeasure
        (shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) := by
  convert sourceUniformInterval_phase_preimage _
    (measurableSet_shiftedAngleCosineBandPhaseSublevel (δ : Real.Angle) q h) using 1
  congr 1

theorem phaseCircleMeasure_shiftedAngleCosineBandPhaseSublevel_eq
    (δ : AddCircle (2 * Real.pi)) (q h : ℝ) :
    phaseCircleMeasure (shiftedAngleCosineBandPhaseSublevel δ q h) =
      phaseCircleMeasure (angleCosineBandPhaseSublevel q h) := by
  unfold phaseCircleMeasure
  rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul,
    volume_shiftedAngleCosineBandPhaseSublevel_eq]

/-- Translation invariance extends the cosine-band estimate to any phase
offset. -/
theorem sourceUniformInterval_shiftedCosineBandPhaseSublevel_le_sqrt
    (δ q h : ℝ) (hh : 0 ≤ h) :
    sourceUniformInterval 0 (2 * Real.pi)
        (shiftedCosineBandPhaseSublevel δ q h) ≤ ENNReal.ofReal (Real.sqrt h) := by
  rw [sourceUniformInterval_shiftedCosineBandPhaseSublevel_eq_phaseCircleMeasure]
  change phaseCircleMeasure
      (shiftedAngleCosineBandPhaseSublevel (δ : AddCircle (2 * Real.pi)) q h) ≤ _
  rw [phaseCircleMeasure_shiftedAngleCosineBandPhaseSublevel_eq,
    ← sourceUniformInterval_cosineBandPhaseSublevel_eq_phaseCircleMeasure]
  exact sourceUniformInterval_cosineBandPhaseSublevel_le_sqrt q h hh

/-- The deterministic trigonometric term in the second branch of Lemma 3.6. -/
def affineTrig (a b c φ : ℝ) : ℝ :=
  a + b * Real.cos φ + c * Real.sin φ

private def affineTrigPhaseCoefficient (b c : ℝ) : ℂ :=
  (b : ℂ) - (c : ℂ) * Complex.I

def affineTrigAmplitude (b c : ℝ) : ℝ := Real.sqrt (b ^ 2 + c ^ 2)

def affineTrigPhase (b c : ℝ) : ℝ :=
  Complex.arg (affineTrigPhaseCoefficient b c)

/-- Polar normalization of the full affine trigonometric polynomial. -/
theorem affineTrig_cosine_normalForm (a b c φ : ℝ) :
    affineTrig a b c φ =
      a + affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ) := by
  let z : ℂ := (b : ℂ) - (c : ℂ) * Complex.I
  have hn : ‖z‖ = affineTrigAmplitude b c := by
    simp [z, affineTrigAmplitude, Complex.norm_def, Complex.normSq_apply, pow_two]
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [hn] at hc hs
  simp [z] at hc hs
  change a + b * Real.cos φ + c * Real.sin φ = a + affineTrigAmplitude b c * Real.cos (z.arg + φ)
  rw [Real.cos_add, mul_sub, ← mul_assoc, ← mul_assoc, hc, hs]
  ring

theorem affineTrigAmplitude_sq (b c : ℝ) :
    affineTrigAmplitude b c ^ 2 = b ^ 2 + c ^ 2 := by
  unfold affineTrigAmplitude
  exact Real.sq_sqrt (by positivity)

theorem affineTrigAmplitude_nonneg (b c : ℝ) :
    0 ≤ affineTrigAmplitude b c := Real.sqrt_nonneg _

/-- The absolute affine-trigonometric sublevel event on one source phase
period. -/
def affineTrigPhaseSublevel (a b c t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |affineTrig a b c φ| ≤ t}

theorem measurableSet_affineTrigPhaseSublevel (a b c t : ℝ) :
    MeasurableSet (affineTrigPhaseSublevel a b c t) := by
  unfold affineTrigPhaseSublevel affineTrig
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.add (measurable_const.mul Real.continuous_cos.measurable)).add
      (measurable_const.mul Real.continuous_sin.measurable)).abs)
    measurable_const

theorem affineTrigPhaseSublevel_subset_shiftedCosineBand
    (a b c t : ℝ) (hR : 0 < affineTrigAmplitude b c) :
    affineTrigPhaseSublevel a b c t ⊆
      shiftedCosineBandPhaseSublevel (affineTrigPhase b c)
        (-a / affineTrigAmplitude b c) (t / affineTrigAmplitude b c) := by
  intro φ hφ
  change φ ∈ Icc 0 (2 * Real.pi) ∧ |affineTrig a b c φ| ≤ t at hφ
  constructor
  · exact hφ.1
  rw [affineTrig_cosine_normalForm] at hφ
  have hfactor : a + affineTrigAmplitude b c *
      Real.cos (affineTrigPhase b c + φ) =
      affineTrigAmplitude b c *
        (Real.cos (affineTrigPhase b c + φ) -
          (-a / affineTrigAmplitude b c)) := by
    field_simp [hR.ne']
    ring
  rw [hfactor, abs_mul, abs_of_pos hR] at hφ
  apply (le_div_iff₀ hR).mpr
  simpa only [mul_comm] using hφ.2

/-- The phase-band result instantiated for a nonzero affine trigonometric
polynomial. -/
theorem sourceUniformInterval_affineTrigPhaseSublevel_le_sqrt_div
    (a b c t : ℝ) (ht : 0 ≤ t) (hR : 0 < affineTrigAmplitude b c) :
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
      ENNReal.ofReal (Real.sqrt (t / affineTrigAmplitude b c)) := by
  calc
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
        sourceUniformInterval 0 (2 * Real.pi)
          (shiftedCosineBandPhaseSublevel (affineTrigPhase b c)
            (-a / affineTrigAmplitude b c) (t / affineTrigAmplitude b c)) :=
      measure_mono (affineTrigPhaseSublevel_subset_shiftedCosineBand a b c t hR)
    _ ≤ ENNReal.ofReal (Real.sqrt (t / affineTrigAmplitude b c)) :=
      sourceUniformInterval_shiftedCosineBandPhaseSublevel_le_sqrt _ _ _
        (div_nonneg ht hR.le)

theorem abs_affineTrig_sub_const_le_amplitude (a b c φ : ℝ) :
    |affineTrig a b c φ - a| ≤ affineTrigAmplitude b c := by
  rw [affineTrig_cosine_normalForm]
  have hR : 0 ≤ affineTrigAmplitude b c := affineTrigAmplitude_nonneg b c
  calc
    |a + affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ) - a| =
        |affineTrigAmplitude b c * Real.cos (affineTrigPhase b c + φ)| := by
      congr 1
      ring
    _ = affineTrigAmplitude b c * |Real.cos (affineTrigPhase b c + φ)| := by
      rw [abs_mul, abs_of_nonneg hR]
    _ ≤ affineTrigAmplitude b c * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) hR
    _ = affineTrigAmplitude b c := by ring

/-- In the small-amplitude alternative of the source proof, coefficient
energy forces the affine trigonometric polynomial away from zero. -/
theorem affineTrig_abs_ge_half_of_small_amplitude
    (a b c φ : ℝ)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2)
    (hamp : affineTrigAmplitude b c ≤ 1 / 4) :
    (1 / 2 : ℝ) ≤ |affineTrig a b c φ| := by
  have hR0 : 0 ≤ affineTrigAmplitude b c := affineTrigAmplitude_nonneg b c
  have hRsq : affineTrigAmplitude b c ^ 2 ≤ (1 / 16 : ℝ) := by
    nlinarith
  have htailSq : b ^ 2 + c ^ 2 ≤ (1 / 16 : ℝ) := by
    rw [← affineTrigAmplitude_sq]
    exact hRsq
  have haSq : (3 / 4 : ℝ) ^ 2 ≤ a ^ 2 := by
    nlinarith
  have haAbs : (3 / 4 : ℝ) ≤ |a| := by
    apply (sq_le_sq₀ (by norm_num) (abs_nonneg a)).mp
    simpa only [sq_abs] using haSq
  have hdev : |affineTrig a b c φ - a| ≤ affineTrigAmplitude b c :=
    abs_affineTrig_sub_const_le_amplitude a b c φ
  have htri : |a| ≤ |affineTrig a b c φ| +
      |affineTrig a b c φ - a| := by
    calc
      |a| = |affineTrig a b c φ + (a - affineTrig a b c φ)| := by
        congr 1
        ring
      _ ≤ |affineTrig a b c φ| + |a - affineTrig a b c φ| := abs_add_le _ _
      _ = |affineTrig a b c φ| + |affineTrig a b c φ - a| := by
        rw [abs_sub_comm]
  nlinarith

theorem affineTrigPhaseSublevel_subset_empty_of_small_amplitude
    (a b c t : ℝ)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2)
    (hamp : affineTrigAmplitude b c ≤ 1 / 4)
    (ht : t < 1 / 2) :
    affineTrigPhaseSublevel a b c t ⊆ ∅ := by
  intro φ hφ
  have hlarge : (1 / 2 : ℝ) ≤ |affineTrig a b c φ| :=
    affineTrig_abs_ge_half_of_small_amplitude a b c φ hcoeff hamp
  exact (not_le_of_gt ht) (hlarge.trans hφ.2)

/-- The source's second (non-tail) branch: an absolute affine
trigonometric polynomial whose coefficient energy is bounded below has
one-period small-ball probability `O(Real.sqrt t)`.  The exponent is sharp at a
quadratic phase zero. -/
theorem sourceUniformInterval_affineTrigPhaseSublevel_le_two_sqrt
    (a b c t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
      ENNReal.ofReal (2 * Real.sqrt t) := by
  rcases le_total (affineTrigAmplitude b c) (1 / 4 : ℝ) with hamp | hamp
  · rcases lt_or_ge t (1 / 2 : ℝ) with htSmall | htLarge
    · calc
        sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
            sourceUniformInterval 0 (2 * Real.pi) ∅ :=
          measure_mono (affineTrigPhaseSublevel_subset_empty_of_small_amplitude
            a b c t hcoeff hamp htSmall)
        _ = 0 := measure_empty
        _ ≤ ENNReal.ofReal (2 * Real.sqrt t) := bot_le
    · have hsqrt : (1 / 2 : ℝ) ≤ Real.sqrt t := by
        apply (Real.le_sqrt (by norm_num) ht).mpr
        nlinarith
      calc
        sourceUniformInterval 0 (2 * Real.pi) (affineTrigPhaseSublevel a b c t) ≤
            sourceUniformInterval 0 (2 * Real.pi) (Icc 0 (2 * Real.pi)) := by
          apply measure_mono
          intro φ hφ
          exact hφ.1
        _ = 1 := sourceUniformInterval_apply_self (by positivity)
        _ = ENNReal.ofReal 1 := by norm_num
        _ ≤ ENNReal.ofReal (2 * Real.sqrt t) :=
          ENNReal.ofReal_le_ofReal (by linarith)
  · have hRpos : 0 < affineTrigAmplitude b c :=
      lt_of_lt_of_le (by norm_num) hamp
    have hquot : t / affineTrigAmplitude b c ≤ 4 * t := by
      calc
        t / affineTrigAmplitude b c ≤ t / (1 / 4 : ℝ) :=
          div_le_div_of_nonneg_left ht (by norm_num) hamp
        _ = 4 * t := by ring
    have hsqrt : Real.sqrt (t / affineTrigAmplitude b c) ≤ 2 * Real.sqrt t := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
      calc
        Real.sqrt (t / affineTrigAmplitude b c) ^ 2 =
            t / affineTrigAmplitude b c :=
          Real.sq_sqrt (div_nonneg ht hRpos.le)
        _ ≤ 4 * t := hquot
        _ = (2 * Real.sqrt t) ^ 2 := by
          calc
            4 * t = 4 * Real.sqrt t ^ 2 := by rw [Real.sq_sqrt ht]
            _ = (2 * Real.sqrt t) ^ 2 := by ring
    exact (sourceUniformInterval_affineTrigPhaseSublevel_le_sqrt_div
      a b c t ht hRpos).trans (ENNReal.ofReal_le_ofReal hsqrt)

/-- The scalar phase term in equation (3.21), written with the source's
normalization.  Its constant coefficient is half of the first real
coordinate. -/
def sourceScalarPhase (σ β γ φ : ℝ) : ℝ :=
  σ / 2 + β * Real.cos φ - γ * Real.sin φ

/-- The source-normalized scalar phase sublevel event on one period. -/
def sourceScalarPhaseSublevel (σ β γ t : ℝ) : Set ℝ :=
  {φ : ℝ | φ ∈ Icc 0 (2 * Real.pi) ∧ |sourceScalarPhase σ β γ φ| ≤ t}

theorem measurableSet_sourceScalarPhaseSublevel (σ β γ t : ℝ) :
    MeasurableSet (sourceScalarPhaseSublevel σ β γ t) := by
  unfold sourceScalarPhaseSublevel sourceScalarPhase
  apply measurableSet_Icc.inter
  exact measurableSet_le
    (((measurable_const.add (measurable_const.mul Real.continuous_cos.measurable)).sub
      (measurable_const.mul Real.continuous_sin.measurable)).abs)
    measurable_const

theorem affineTrig_scaled_eq_two_mul_sourceScalarPhase (σ β γ φ : ℝ) :
    affineTrig σ (2 * β) (-2 * γ) φ =
      2 * sourceScalarPhase σ β γ φ := by
  unfold affineTrig sourceScalarPhase
  ring

/-- To invoke the coefficient-energy phase theorem on the source scalar
term, one must first multiply it by two.  This avoids incorrectly treating
the source coefficient `σ / 2` as if it carried full `σ²` energy. -/
theorem sourceScalarPhaseSublevel_eq_affineTrigPhaseSublevel
    (σ β γ t : ℝ) :
    sourceScalarPhaseSublevel σ β γ t =
      affineTrigPhaseSublevel σ (2 * β) (-2 * γ) (2 * t) := by
  ext φ
  unfold sourceScalarPhaseSublevel affineTrigPhaseSublevel
  simp only [Set.mem_ofPred_eq]
  rw [affineTrig_scaled_eq_two_mul_sourceScalarPhase]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  constructor <;> intro h
  · exact ⟨h.1, by nlinarith [h.2]⟩
  · exact ⟨h.1, by nlinarith [h.2]⟩

/-- The source's non-tail scalar branch, in precisely the normalization of
equation (3.21).  Multiplying by two transfers the stated coefficient-energy
assumption to the affine-trigonometric estimate. -/
theorem sourceUniformInterval_sourceScalarPhaseSublevel_le_two_sqrt_two_mul
    (σ β γ t : ℝ) (ht : 0 ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ σ ^ 2 + β ^ 2 + γ ^ 2) :
    sourceUniformInterval 0 (2 * Real.pi)
        (sourceScalarPhaseSublevel σ β γ t) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) := by
  rw [sourceScalarPhaseSublevel_eq_affineTrigPhaseSublevel]
  apply sourceUniformInterval_affineTrigPhaseSublevel_le_two_sqrt
  · linarith
  · nlinarith [sq_nonneg β, sq_nonneg γ]

end NLA.FR05
