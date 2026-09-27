/-
The tail-dominated conditional small-ball step of Lemma 3.6.

For a fixed radial coordinate, this module combines the affine-cosine phase
sublevel estimate with the exact one-dimensional Gaussian projection bound.
It works under the source uniform phase times independent complex-Gaussian
tail law, retaining the source scaling `sqrt (2 / S)` explicitly before
simplifying it to the familiar `sqrt S / t` factor.
-/
import NLA.FR05.SmallBall.GaussianProjectionSmallBall
import NLA.FR05.SmallBall.TailVariancePhase

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Splitting a product event into a bad left-coordinate set and uniformly
bounded good sections gives the sum of the two bounds. -/
theorem prod_measure_le_add_of_bad_sections
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set (α × β)} (hs : MeasurableSet s)
    {bad : Set α} (hbad_meas : MeasurableSet bad)
    (b c : ℝ≥0∞)
    (hbad : μ bad ≤ b)
    (hsection : ∀ x : α, x ∉ bad → ν {y | (x, y) ∈ s} ≤ c) :
    (μ.prod ν) s ≤ b + c := by
  let goodPart : Set (α × β) := s ∩ (badᶜ ×ˢ Set.univ)
  have hgoodPart : MeasurableSet goodPart :=
    hs.inter (hbad_meas.compl.prod MeasurableSet.univ)
  have hsubset : s ⊆ (bad ×ˢ Set.univ) ∪ goodPart := by
    rintro ⟨x, y⟩ hxy
    by_cases hx : x ∈ bad
    · exact Or.inl ⟨hx, mem_univ y⟩
    · exact Or.inr ⟨hxy, ⟨hx, mem_univ y⟩⟩
  calc
    (μ.prod ν) s ≤ (μ.prod ν) ((bad ×ˢ Set.univ) ∪ goodPart) :=
      measure_mono hsubset
    _ ≤ (μ.prod ν) (bad ×ˢ Set.univ) + (μ.prod ν) goodPart :=
      measure_union_le _ _
    _ ≤ b + c := by
      gcongr
      · rw [MeasureTheory.Measure.prod_prod]
        simpa using hbad
      · apply prod_measure_le_of_sections_le μ ν hgoodPart c
        intro x
        by_cases hx : x ∈ bad
        · simp [goodPart, hx]
        · exact (measure_mono (by
            intro y hy
            exact hy.1)).trans (hsection x hx)

/-- The conditional small-ball event for the Gaussian tail term in (3.21),
with the source phase support written into the set.  Including the support is
convenient: outside it every tail section is empty. -/
def tailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (S a u : ℝ) : Set (ℝ × Signal n) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |a + Real.sqrt (2 / S) *
      (star x.2 ⬝ᵥ (p + Complex.exp ((x.1 : ℂ) * Complex.I) • q)).re| ≤ u}

theorem measurableSet_tailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (S a u : ℝ) :
    MeasurableSet (tailConditionalSmallBallEvent p q S a u) := by
  unfold tailConditionalSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × Signal n ↦ |a + Real.sqrt (2 / S) *
        (star x.2 ⬝ᵥ (p + Complex.exp ((x.1 : ℂ) * Complex.I) • q)).re|) ⁻¹' Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    fun_prop

/-- At a fixed source phase whose tail variance is at least `t²`, the
Gaussian tail contribution to (3.21) has the one-dimensional small-ball
bound.  The displayed denominator keeps the exact rescaling visible; it is
algebraically `2 * u * sqrt S / (sqrt (2*pi) * t)`. -/
theorem tailConditionalSmallBall_section_le
    {n : ℕ} (p q : Signal n) (S a u t φ : ℝ)
    (hS : 0 < S) (hu : 0 ≤ u) (ht : 0 < t)
    (hvariance : t ^ 2 ≤ tailVarianceProfile p q φ) :
    standardComplexGaussianTail n
        {w | |a + Real.sqrt (2 / S) *
          (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u} ≤
      ENNReal.ofReal
        (2 * (u / Real.sqrt (2 / S)) /
          (Real.sqrt (2 * Real.pi) * (t / Real.sqrt 2))) := by
  let c : ℝ := Real.sqrt (2 / S)
  have hc : 0 < c := by
    unfold c
    apply Real.sqrt_pos.2
    exact div_pos (by norm_num) hS
  have hset :
      {w : Signal n | |a + c *
        (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u} =
        {w | |(star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re -
          (-a / c)| ≤ u / c} := by
    ext w
    let y : ℝ :=
      (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re
    change |a + c * y| ≤ u ↔ |y - (-a / c)| ≤ u / c
    have hy : y - (-a / c) = (a + c * y) / c := by
      field_simp
      ring
    rw [hy, abs_div, abs_of_pos hc]
    exact (div_le_div_iff_of_pos_right hc).symm
  change standardComplexGaussianTail n
      {w | |a + c *
        (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
  rw [hset]
  apply standardComplexGaussianTail_smallBall
  · exact div_nonneg hu hc.le
  · exact div_pos ht (Real.sqrt_pos.2 (by norm_num))
  · have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    rw [div_pow, hsqrt]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).mpr
    simpa only [tailVarianceProfile, tailEnergy_eq_signalEnergy] using hvariance

theorem tailConditionalSmallBall_rescaled_bound_eq (S u t : ℝ)
    (hS : 0 < S) (ht : 0 < t) :
    2 * (u / Real.sqrt (2 / S)) /
        (Real.sqrt (2 * Real.pi) * (t / Real.sqrt 2)) =
      2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2) S]
  have hsqrtS : Real.sqrt S ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hS)
  have hsqrtTwo : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hsqrtTwoPi : Real.sqrt (2 * Real.pi) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  field_simp

theorem measurableSet_tailVariancePhaseSublevel {n : ℕ}
    (p q : Signal n) (t : ℝ) :
    MeasurableSet (tailVariancePhaseSublevel p q t) := by
  unfold tailVariancePhaseSublevel
  apply MeasurableSet.inter
  · exact measurableSet_Icc
  · change MeasurableSet ((tailVarianceProfile p q) ⁻¹' Iic (t ^ 2))
    apply MeasurableSet.preimage measurableSet_Iic
    unfold tailVarianceProfile tailEnergy
    fun_prop

/-- The tail-dominated conditional step of Lemma 3.6, over the actual
uniform source phase times independent complex-Gaussian tail law.  The first
term is the exceptional low-variance phase set and the second is the exact
one-dimensional Gaussian interval bound on its complement. -/
theorem sourceUniformInterval_prod_tailConditionalSmallBall_le
    {n : ℕ} (p q : Signal n) (S a u t : ℝ)
    (hS : 0 < S) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (tailConditionalSmallBallEvent p q S a u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * (u / Real.sqrt (2 / S)) /
            (Real.sqrt (2 * Real.pi) * (t / Real.sqrt 2))) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let htail : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  apply @prod_measure_le_add_of_bad_sections ℝ (Signal n) _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (standardComplexGaussianTail n) hphase htail
    (tailConditionalSmallBallEvent p q S a u)
    (measurableSet_tailConditionalSmallBallEvent p q S a u)
    (tailVariancePhaseSublevel p q t)
    (measurableSet_tailVariancePhaseSublevel p q t)
    (ENNReal.ofReal (4 * t))
    (ENNReal.ofReal
      (2 * (u / Real.sqrt (2 / S)) /
        (Real.sqrt (2 * Real.pi) * (t / Real.sqrt 2))))
  · exact sourceUniformInterval_tailVariancePhaseSublevel_le_four_mul_of_energy
      p q t ht.le henergy
  · intro φ hφ
    by_cases hsupport : φ ∈ Icc 0 (2 * Real.pi)
    · have hnotle : ¬ tailVarianceProfile p q φ ≤ t ^ 2 := by
        intro hle
        exact hφ ⟨hsupport, hle⟩
      have hvariance : t ^ 2 ≤ tailVarianceProfile p q φ :=
        (lt_of_not_ge hnotle).le
      change standardComplexGaussianTail n
          {w | φ ∈ Icc 0 (2 * Real.pi) ∧
            |a + Real.sqrt (2 / S) *
              (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
      simp only [hsupport, true_and]
      exact tailConditionalSmallBall_section_le p q S a u t φ hS hu ht hvariance
    · have hempty :
        {w : Signal n | (φ, w) ∈ tailConditionalSmallBallEvent p q S a u} = ∅ := by
          ext w
          change (φ ∈ Icc 0 (2 * Real.pi) ∧
            |a + Real.sqrt (2 / S) *
              (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u) ↔
            w ∈ (∅ : Set (Signal n))
          simp only [hsupport, false_and]
          exact (Set.mem_empty_iff_false w).symm
      rw [hempty, measure_empty]
      exact bot_le

/-- The same conditional estimate with the Gaussian scale simplified to the
form used in the proof: `2u sqrt(S) / (sqrt(2π)t)`. -/
theorem sourceUniformInterval_prod_tailConditionalSmallBall_le_rescaled
    {n : ℕ} (p q : Signal n) (S a u t : ℝ)
    (hS : 0 < S) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (tailConditionalSmallBallEvent p q S a u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  rw [← tailConditionalSmallBall_rescaled_bound_eq S u t hS ht]
  exact sourceUniformInterval_prod_tailConditionalSmallBall_le p q S a u t
    hS hu ht henergy

/-- Version of the tail event with a measurable phase-dependent deterministic
centre.  This is the shape of the scalar part of equation (3.21). -/
def tailConditionalSmallBallEventOfCenter {n : ℕ}
    (p q : Signal n) (S : ℝ) (a : ℝ → ℝ) (u : ℝ) : Set (ℝ × Signal n) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |a x.1 + Real.sqrt (2 / S) *
      (star x.2 ⬝ᵥ (p + Complex.exp ((x.1 : ℂ) * Complex.I) • q)).re| ≤ u}

theorem measurableSet_tailConditionalSmallBallEventOfCenter {n : ℕ}
    (p q : Signal n) (S : ℝ) (a : ℝ → ℝ) (u : ℝ) (ha : Measurable a) :
    MeasurableSet (tailConditionalSmallBallEventOfCenter p q S a u) := by
  unfold tailConditionalSmallBallEventOfCenter
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × Signal n ↦ |a x.1 + Real.sqrt (2 / S) *
        (star x.2 ⬝ᵥ (p + Complex.exp ((x.1 : ℂ) * Complex.I) • q)).re|) ⁻¹' Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    exact ((ha.comp measurable_fst).add (by fun_prop)).abs

/-- The conditional tail estimate is uniform in the deterministic scalar
centre, so it applies directly to the phase-dependent scalar part of (3.21).
-/
theorem sourceUniformInterval_prod_tailConditionalSmallBallOfCenter_le_rescaled
    {n : ℕ} (p q : Signal n) (S : ℝ) (a : ℝ → ℝ) (u t : ℝ)
    (ha : Measurable a) (hS : 0 < S) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (tailConditionalSmallBallEventOfCenter p q S a u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let htail : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  rw [← tailConditionalSmallBall_rescaled_bound_eq S u t hS ht]
  apply @prod_measure_le_add_of_bad_sections ℝ (Signal n) _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (standardComplexGaussianTail n) hphase htail
    (tailConditionalSmallBallEventOfCenter p q S a u)
    (measurableSet_tailConditionalSmallBallEventOfCenter p q S a u ha)
    (tailVariancePhaseSublevel p q t)
    (measurableSet_tailVariancePhaseSublevel p q t)
    (ENNReal.ofReal (4 * t))
    (ENNReal.ofReal
      (2 * (u / Real.sqrt (2 / S)) /
        (Real.sqrt (2 * Real.pi) * (t / Real.sqrt 2))))
  · exact sourceUniformInterval_tailVariancePhaseSublevel_le_four_mul_of_energy
      p q t ht.le henergy
  · intro φ hφ
    by_cases hsupport : φ ∈ Icc 0 (2 * Real.pi)
    · have hnotle : ¬ tailVarianceProfile p q φ ≤ t ^ 2 := by
        intro hle
        exact hφ ⟨hsupport, hle⟩
      have hvariance : t ^ 2 ≤ tailVarianceProfile p q φ :=
        (lt_of_not_ge hnotle).le
      change standardComplexGaussianTail n
          {w | φ ∈ Icc 0 (2 * Real.pi) ∧
            |a φ + Real.sqrt (2 / S) *
              (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
      simp only [hsupport, true_and]
      exact tailConditionalSmallBall_section_le p q S (a φ) u t φ hS hu ht hvariance
    · have hempty :
        {w : Signal n | (φ, w) ∈ tailConditionalSmallBallEventOfCenter p q S a u} = ∅ := by
          ext w
          change (φ ∈ Icc 0 (2 * Real.pi) ∧
            |a φ + Real.sqrt (2 / S) *
              (star w ⬝ᵥ (p + Complex.exp ((φ : ℂ) * Complex.I) • q)).re| ≤ u) ↔
            w ∈ (∅ : Set (Signal n))
          simp only [hsupport, false_and]
          exact (Set.mem_empty_iff_false w).symm
      rw [hempty, measure_empty]
      exact bot_le

/-- The literal tail term in (3.21), before moving the first planted phase
from the Gaussian tail onto the deterministic direction. -/
def phaseNormalizedTailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (α S : ℝ) (a : ℝ → ℝ) (u : ℝ) : Set (ℝ × Signal n) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |a x.1 + Real.sqrt (2 / S) *
      (star (Complex.exp ((-α : ℂ) * Complex.I) • x.2) ⬝ᵥ
        (p + Complex.exp (((x.1 - α : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u}

theorem tailEnergy_phaseRotate {n : ℕ} (α : ℝ) (p : Signal n) :
    tailEnergy (Complex.exp ((α : ℂ) * Complex.I) • p) = tailEnergy p := by
  exact signalEnergy_phaseRotate α p

/-- Moving `exp (-α I)` from the tail to the direction turns the phase gap
into the sampled second phase.  This is the source-coordinate normalization
needed to apply the preceding uniform-phase estimate without changing law. -/
theorem phaseNormalizedTailConditionalSmallBallEvent_eq_ofCenter {n : ℕ}
    (p q : Signal n) (α S : ℝ) (a : ℝ → ℝ) (u : ℝ) :
    phaseNormalizedTailConditionalSmallBallEvent p q α S a u =
      tailConditionalSmallBallEventOfCenter
        (Complex.exp ((α : ℂ) * Complex.I) • p) q S a u := by
  ext x
  have hdirection :
      Complex.exp ((α : ℂ) * Complex.I) •
          (p + Complex.exp (((x.1 - α : ℝ) : ℂ) * Complex.I) • q) =
        Complex.exp ((α : ℂ) * Complex.I) • p +
          Complex.exp ((x.1 : ℂ) * Complex.I) • q := by
    have hexp :
        Complex.exp ((x.1 : ℂ) * Complex.I) =
          Complex.exp ((α : ℂ) * Complex.I) *
            Complex.exp (((x.1 - α : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    ext j
    simp only [Pi.smul_apply, Pi.add_apply]
    rw [hexp]
    ring
  have hdot := phaseRotate_real_dotProduct α x.2
    (p + Complex.exp (((x.1 - α : ℝ) : ℂ) * Complex.I) • q)
  simp only [phaseNormalizedTailConditionalSmallBallEvent,
    tailConditionalSmallBallEventOfCenter, Set.mem_ofPred_eq]
  rw [hdot, hdirection]

/-- The preceding conditional bound applies directly to the original
phase-normalized source tail from (3.21), for every fixed first phase `α`.
-/
theorem sourceUniformInterval_prod_phaseNormalizedTailConditionalSmallBallOfCenter_le_rescaled
    {n : ℕ} (p q : Signal n) (α S : ℝ) (a : ℝ → ℝ) (u t : ℝ)
    (ha : Measurable a) (hS : 0 < S) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (phaseNormalizedTailConditionalSmallBallEvent p q α S a u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) := by
  rw [phaseNormalizedTailConditionalSmallBallEvent_eq_ofCenter]
  apply sourceUniformInterval_prod_tailConditionalSmallBallOfCenter_le_rescaled
  · exact ha
  · exact hS
  · exact hu
  · exact ht
  · rw [tailEnergy_phaseRotate]
    exact henergy

end NLA.FR05
