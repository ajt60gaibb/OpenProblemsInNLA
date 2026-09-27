import NLA.FR05.SmallBall.SourceScalarShift
import NLA.FR05.SmallBall.SourceTail

/-!
# Global and conditional non-tail small-ball bounds

The sections develop `SourceNonTailConditional`, `SourceNonTailGlobal`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section SourceNonTailConditional

/-
The source-faithful non-tail conditional small-ball branch of Lemma 3.6.

For a fixed radial coordinate and first phase, the deterministic centre is
controlled by the shifted scalar phase estimate. On its complement, the
complex-Gaussian tail is controlled by a variance-uniform projection bound.
No lower bound on the tail variance is imposed in this branch.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The literal source Jacobian small-ball event over the second phase and
Gaussian tail, conditional on a radial coordinate and first phase. -/
def sourceNonTailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma beta gamma S alpha u : ℝ) : Set (ℝ × Signal n) :=
  {x | x.1 ∈ Icc 0 (2 * Real.pi) ∧
    |sourceJacobianPhaseCenter sigma beta gamma alpha x.1 +
      Real.sqrt (2 / S) *
        (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
          (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u}

theorem measurableSet_sourceNonTailConditionalSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma beta gamma S alpha u : ℝ) :
    MeasurableSet
      (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) := by
  unfold sourceNonTailConditionalSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc measurable_fst
  · change MeasurableSet
      ((fun x : ℝ × Signal n ↦
        |sourceJacobianPhaseCenter sigma beta gamma alpha x.1 +
          Real.sqrt (2 / S) *
            (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
              (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re|) ⁻¹'
        Iic u)
    apply MeasurableSet.preimage measurableSet_Iic
    have hcenter : Measurable
        (fun x : ℝ × Signal n ↦
          sourceJacobianPhaseCenter sigma beta gamma alpha x.1) :=
      (measurable_sourceJacobianPhaseCenter sigma beta gamma alpha).comp measurable_fst
    have htail : Measurable
        (fun x : ℝ × Signal n ↦
          Real.sqrt (2 / S) *
            (star (Complex.exp ((-alpha : ℂ) * Complex.I) • x.2) ⬝ᵥ
              (p + Complex.exp (((x.1 - alpha : ℝ) : ℂ) * Complex.I) • q)).re) := by
      fun_prop
    exact (hcenter.add htail).abs

/-- Rotate the first source phase out of the Gaussian tail and absorb the
real radial scale into the complex projection direction. -/
theorem sourceNonTailGaussianTerm_eq_real_dotProduct
    {n : ℕ} (p q w : Signal n) (S alpha phi : ℝ) :
    Real.sqrt (2 / S) *
        (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
          (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re =
      (star w ⬝ᵥ
        ((Real.sqrt (2 / S) : ℂ) •
          (Complex.exp ((alpha : ℂ) * Complex.I) •
            (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)))).re := by
  rw [phaseRotate_real_dotProduct]
  rw [dotProduct_smul, dotProduct_smul]
  conv_rhs => rw [smul_eq_mul, Complex.re_ofReal_mul]
  rw [dotProduct_smul]

/-- Conditional non-tail small-ball estimate for the literal source row.
The exceptional phase set has the source `sqrt(t)` bound, while every
remaining Gaussian-tail section has a uniform `u / t` bound. -/
theorem sourceUniformInterval_prod_sourceNonTailConditionalSmallBall_le
    {n : ℕ} (p q : Signal n) (sigma beta gamma S alpha u t : ℝ)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    ((sourceUniformInterval 0 (2 * Real.pi)).prod (standardComplexGaussianTail n))
        (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let hphase : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let htail : IsProbabilityMeasure (standardComplexGaussianTail n) :=
    isProbabilityMeasure_standardComplexGaussianTail n
  apply @prod_measure_le_add_of_bad_sections ℝ (Signal n) _ _
    (sourceUniformInterval 0 (2 * Real.pi)) (standardComplexGaussianTail n) hphase htail
    (sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u)
    (measurableSet_sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u)
    (sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t)
    (measurableSet_sourceJacobianPhaseCenterSublevel sigma beta gamma alpha t)
    (ENNReal.ofReal (2 * Real.sqrt (2 * t)))
    (ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)))
  · exact sourceUniformInterval_sourceJacobianPhaseCenterSublevel_le_two_sqrt_two_mul
      sigma beta gamma alpha t ht.le hcoeff
  · intro phi hphi
    by_cases hsupport : phi ∈ Icc 0 (2 * Real.pi)
    · have hnotle :
        ¬ |sourceJacobianPhaseCenter sigma beta gamma alpha phi| ≤ t := by
          intro hle
          exact hphi ⟨hsupport, hle⟩
      have hcentre : t ≤ |sourceJacobianPhaseCenter sigma beta gamma alpha phi| :=
        (lt_of_not_ge hnotle).le
      change standardComplexGaussianTail n
          {w : Signal n | phi ∈ Icc 0 (2 * Real.pi) ∧
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                  (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
      simp only [hsupport, true_and]
      let z : Signal n :=
        (Real.sqrt (2 / S) : ℂ) •
          (Complex.exp ((alpha : ℂ) * Complex.I) •
            (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q))
      have hset :
          {w : Signal n |
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                  (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u} =
            {w : Signal n |
              |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
                (star w ⬝ᵥ z).re| ≤ u} := by
        ext w
        change
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u ↔
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              (star w ⬝ᵥ z).re| ≤ u
        dsimp [z]
        change
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u ↔
            |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
              (star w ⬝ᵥ
                ((Real.sqrt (2 / S) : ℂ) •
                  (Complex.exp ((alpha : ℂ) * Complex.I) •
                    (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)))).re| ≤ u
        rw [sourceNonTailGaussianTerm_eq_real_dotProduct]
      rw [hset]
      exact standardComplexGaussianTail_real_dotProduct_abs_add_smallBall_uniform
        z (sourceJacobianPhaseCenter sigma beta gamma alpha phi) u t ht hcentre hscale
    · have hempty :
        {w : Signal n | (phi, w) ∈
          sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u} = ∅ := by
        ext w
        change (phi ∈ Icc 0 (2 * Real.pi) ∧
          |sourceJacobianPhaseCenter sigma beta gamma alpha phi +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-alpha : ℂ) * Complex.I) • w) ⬝ᵥ
                (p + Complex.exp (((phi - alpha : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u) ↔
          w ∈ (∅ : Set (Signal n))
        simp [hsupport]
      rw [hempty, measure_empty]
      exact bot_le

end SourceNonTailConditional

section SourceNonTailGlobal

/-
Outer source-law assembly for the scalar-dominated branch of Lemma 3.6.

The conditional non-tail calculation is uniform in the radial coordinate,
imbalance, and first phase. This file reassociates the exact five-factor
source law and integrates those independent factors without replacing the
source distribution by a surrogate.
-/


open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The scalar-dominated source-row event in the right-associated coordinate
order `S, xi, alpha, (phi, w)`. The first-phase support is included so that
off-support sections are empty. -/
def sourceNonTailSmallBallEventRight {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) :
    Set (ℝ × (ℝ × (ℝ × (ℝ × Signal n)))) :=
  {x | x.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
    x.2.2.2 ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma
      x.1 x.2.2.1 u}

theorem measurableSet_sourceNonTailSmallBallEventRight {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) :
    MeasurableSet (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
  unfold sourceNonTailSmallBallEventRight sourceNonTailConditionalSmallBallEvent
  apply MeasurableSet.inter
  · exact MeasurableSet.preimage measurableSet_Icc (by fun_prop)
  · apply MeasurableSet.inter
    · exact MeasurableSet.preimage measurableSet_Icc (by fun_prop)
    · change MeasurableSet
        ((fun x : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) ↦
          |sourceJacobianPhaseCenter sigma beta gamma x.2.2.1 x.2.2.2.1 +
            Real.sqrt (2 / x.1) *
              (star (Complex.exp ((-x.2.2.1 : ℂ) * Complex.I) • x.2.2.2.2) ⬝ᵥ
                (p + Complex.exp (((x.2.2.2.1 - x.2.2.1 : ℝ) : ℂ) * Complex.I) • q)).re|) ⁻¹'
          Iic u)
      apply MeasurableSet.preimage measurableSet_Iic
      unfold sourceJacobianPhaseCenter
      fun_prop

/-- Integrate the scalar-dominated conditional estimate through the three
outer independent source factors. -/
theorem sourceCoordinateLawRight_sourceNonTailSmallBall_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLawRight eta delta epsilon n
        (sourceNonTailSmallBallEventRight p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  let muS := sourceRadialLaw eta delta
  let muxi := sourceUniformInterval (-epsilon) epsilon
  let mualpha := sourceUniformInterval 0 (2 * Real.pi)
  let muphi := sourceUniformInterval 0 (2 * Real.pi)
  let nu := standardComplexGaussianTail n
  let : IsProbabilityMeasure muS := by
    dsimp [muS]
    exact isProbabilityMeasure_sourceRadialLaw heta0 heta1
  let : IsProbabilityMeasure muxi := by
    dsimp [muxi]
    exact isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure mualpha := by
    dsimp [mualpha]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure muphi := by
    dsimp [muphi]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure nu := by
    dsimp [nu]
    exact isProbabilityMeasure_standardComplexGaussianTail n
  change (muS.prod (muxi.prod (mualpha.prod (muphi.prod nu))))
      (sourceNonTailSmallBallEventRight p q sigma beta gamma u) ≤ _
  apply prod_measure_le_of_sections_le muS (muxi.prod (mualpha.prod (muphi.prod nu)))
    (measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u) _
  intro S
  have hSsection : MeasurableSet
      {x : ℝ × (ℝ × (ℝ × Signal n)) |
        (S, x) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u} :=
    measurable_prodMk_left
      (measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u)
  apply prod_measure_le_of_sections_le muxi (mualpha.prod (muphi.prod nu)) hSsection _
  intro xi
  have hxisection : MeasurableSet
      {x : ℝ × (ℝ × Signal n) |
        (xi, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
          (S, y) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u}} :=
    measurable_prodMk_left hSsection
  apply prod_measure_le_of_sections_le mualpha (muphi.prod nu) hxisection _
  intro alpha
  by_cases halpha : alpha ∈ Icc 0 (2 * Real.pi)
  · change (muphi.prod nu)
      {z | alpha ∈ Icc 0 (2 * Real.pi) ∧
        z ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u} ≤ _
    simp only [halpha, true_and]
    exact sourceUniformInterval_prod_sourceNonTailConditionalSmallBall_le
      p q sigma beta gamma S alpha u t ht hscale hcoeff
  · have hempty :
      {z : ℝ × Signal n |
        (alpha, z) ∈ {x : ℝ × (ℝ × Signal n) |
          (xi, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
            (S, y) ∈ sourceNonTailSmallBallEventRight p q sigma beta gamma u}}} = ∅ := by
        ext z
        change (alpha ∈ Icc 0 (2 * Real.pi) ∧
          z ∈ sourceNonTailConditionalSmallBallEvent p q sigma beta gamma S alpha u) ↔
          z ∈ (∅ : Set (ℝ × Signal n))
        simp [halpha]
    rw [hempty, measure_empty]
    exact bot_le

/-- Pull the right-associated scalar-branch event back to the repository's
native source-coordinate order. -/
def sourceNonTailSmallBallEventOnCoordinates {n : ℕ}
    (p q : Signal n) (sigma beta gamma u : ℝ) : Set (SourcePlantedCoordinates n) :=
  (sourceCoordinateReassoc n) ⁻¹'
    sourceNonTailSmallBallEventRight p q sigma beta gamma u

/-- On source support, the reassociated scalar-branch event is the literal
source-row small-ball event with its two phase support clauses displayed. -/
theorem mem_sourceNonTailSmallBallEventOnCoordinates_iff
    {n : ℕ} (x : SourcePlantedCoordinates n) (hS : 0 < x.1.1)
    (hxi : |x.1.2.1| ≤ 1) (p q : Signal n) (sigma beta gamma u : ℝ) :
    x ∈ sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u ↔
      x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) ∧
        |sourceRowJacobianForm (sourceCoordinatesToPlantedRow x hS hxi)
          sigma beta gamma p q| ≤ u := by
  rfl

/-- Under full source support, the literal row event lies in the exact
scalar-branch coordinate event. -/
theorem ae_sourceRowJacobianSmallBall_subset_nonTail
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1) :
    sourceRowJacobianSmallBallEvent p q sigma beta gamma u
      ≤ᵐ[sourceCoordinateLaw eta delta epsilon n]
        sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u := by
  filter_upwards [ae_sourceCoordinateLaw_fullSupport n heta0 heta1 hepsilon hdelta hepsilon1]
    with x hx
  intro hsmall
  change x ∈ sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u
  rw [mem_sourceNonTailSmallBallEventOnCoordinates_iff
    x hx.1 hx.2.1 p q sigma beta gamma u]
  refine ⟨hx.2.2.1, hx.2.2.2, ?_⟩
  have hsupp : 0 < x.1.1 ∧ |x.1.2.1| ≤ 1 := ⟨hx.1, hx.2.1⟩
  have hdefault : sourceCoordinatesToPlantedRowOrDefault x =
      sourceCoordinatesToPlantedRow x hx.1 hx.2.1 := by
    simp [sourceCoordinatesToPlantedRowOrDefault, hsupp]
  change |sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault x)
    sigma beta gamma p q| ≤ u at hsmall
  rw [hdefault] at hsmall
  exact hsmall

/-- The non-tail scalar branch under the exact source-coordinate law. -/
theorem sourceCoordinateLaw_nonTailSmallBall_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw eta delta epsilon n
        (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  have hmeas := measurableSet_sourceNonTailSmallBallEventRight p q sigma beta gamma u
  calc
    sourceCoordinateLaw eta delta epsilon n
        (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) =
        Measure.map (sourceCoordinateReassoc n) (sourceCoordinateLaw eta delta epsilon n)
          (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
      unfold sourceNonTailSmallBallEventOnCoordinates
      rw [Measure.map_apply (sourceCoordinateReassoc n).measurable hmeas]
    _ = sourceCoordinateLawRight eta delta epsilon n
        (sourceNonTailSmallBallEventRight p q sigma beta gamma u) := by
      rw [sourceCoordinateLaw_map_reassoc eta delta epsilon n heta0 heta1 hepsilon]
    _ ≤ _ := sourceCoordinateLawRight_sourceNonTailSmallBall_le
      eta delta epsilon p q sigma beta gamma u t heta0 heta1 hepsilon ht hscale hcoeff

/-- Literal source-row version of the scalar-dominated small-ball estimate. -/
theorem sourceCoordinateLaw_sourceRowJacobianSmallBall_nonTail_le
    {n : ℕ} (eta delta epsilon : ℝ) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw eta delta epsilon n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  calc
    sourceCoordinateLaw eta delta epsilon n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
        sourceCoordinateLaw eta delta epsilon n
          (sourceNonTailSmallBallEventOnCoordinates p q sigma beta gamma u) :=
      measure_mono_ae (ae_sourceRowJacobianSmallBall_subset_nonTail
        eta delta epsilon p q sigma beta gamma u
        heta0 heta1 hepsilon hdelta hepsilon1)
    _ ≤ _ := sourceCoordinateLaw_nonTailSmallBall_le
      eta delta epsilon p q sigma beta gamma u t
      heta0 heta1 hepsilon ht hscale hcoeff

/-- Manuscript-parameter specialization of the literal scalar-dominated
source-row estimate. -/
theorem sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_nonTail_le
    {M n : ℕ} (hM : 1 ≤ M) (p q : Signal n)
    (sigma beta gamma u t : ℝ)
    (ht : 0 < t) (hscale : 2 * u ≤ t)
    (hcoeff : (3 / 4 : ℝ) ≤ sigma ^ 2 + beta ^ 2 + gamma ^ 2) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent p q sigma beta gamma u) ≤
      ENNReal.ofReal (2 * Real.sqrt (2 * t)) +
        ENNReal.ofReal (6 * u / (Real.sqrt (2 * Real.pi) * t)) := by
  exact sourceCoordinateLaw_sourceRowJacobianSmallBall_nonTail_le
    sourceEta (sourceDelta M) (sourceEpsilon M) p q sigma beta gamma u t
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M hM)
    (sourceDelta_pos M hM) (sourceEpsilon_le_one M hM) ht hscale hcoeff

end SourceNonTailGlobal

end NLA.FR05
