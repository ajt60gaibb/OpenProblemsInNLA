/-
The outer source-law assembly for the tail-dominated branch of Lemma 3.6.

The preceding module proves the phase × Gaussian-tail estimate at fixed
radial coordinate and first phase.  Here the exact source-coordinate product
law is reassociated, the independent `S, ξ, α, β, w` factors are integrated,
and a radial cutoff `0 < S ≤ B` makes the resulting bound uniform.
-/
import NLA.FR05.SmallBall.TailConditionalSmallBall

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The three elementary reassociations which put `β` and `w` into the
innermost product of the actual source-coordinate law. -/
def sourceCoordinateReassocFirst (n : ℕ) :
    (SourcePlantedScalars × Signal n) ≃ᵐ
      ℝ × ((ℝ × (ℝ × ℝ)) × Signal n) :=
  MeasurableEquiv.prodAssoc

def sourceCoordinateReassocSecond (n : ℕ) :
    (ℝ × ((ℝ × (ℝ × ℝ)) × Signal n)) ≃ᵐ
      ℝ × (ℝ × ((ℝ × ℝ) × Signal n)) :=
  (MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodAssoc

def sourceCoordinateReassocThird (n : ℕ) :
    (ℝ × (ℝ × ((ℝ × ℝ) × Signal n))) ≃ᵐ
      ℝ × (ℝ × (ℝ × (ℝ × Signal n))) :=
  (MeasurableEquiv.refl ℝ).prodCongr
    ((MeasurableEquiv.refl ℝ).prodCongr MeasurableEquiv.prodAssoc)

/-- Reassociate `(S, (ξ, (α, β))), w` as `S, (ξ, (α, (β, w)))`. -/
def sourceCoordinateReassoc (n : ℕ) :
    SourcePlantedCoordinates n ≃ᵐ ℝ × (ℝ × (ℝ × (ℝ × Signal n))) :=
  (sourceCoordinateReassocFirst n).trans
    ((sourceCoordinateReassocSecond n).trans (sourceCoordinateReassocThird n))

/-- The source-coordinate law in the right-associated product order used by
the conditional proof below.  It has precisely the same five independent
factors as `sourceCoordinateLaw`. -/
def sourceCoordinateLawRight (η δ ε : ℝ) (n : ℕ) :
    Measure (ℝ × (ℝ × (ℝ × (ℝ × Signal n)))) :=
  (sourceRadialLaw η δ).prod
    ((sourceUniformInterval (-ε) ε).prod
      ((sourceUniformInterval 0 (2 * Real.pi)).prod
        ((sourceUniformInterval 0 (2 * Real.pi)).prod
          (standardComplexGaussianTail n))))

/-- Reassociation is measure preserving for the actual source law. -/
theorem sourceCoordinateLaw_map_reassoc (η δ ε : ℝ) (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    Measure.map (sourceCoordinateReassoc n) (sourceCoordinateLaw η δ ε n) =
      sourceCoordinateLawRight η δ ε n := by
  let μ₀ := sourceRadialLaw η δ
  let μ₁ := sourceUniformInterval (-ε) ε
  let μ₂ := sourceUniformInterval 0 (2 * Real.pi)
  let μ₃ := sourceUniformInterval 0 (2 * Real.pi)
  let μ₄ := standardComplexGaussianTail n
  let : IsProbabilityMeasure μ₀ := by
    dsimp [μ₀]
    exact isProbabilityMeasure_sourceRadialLaw hη0 hη1
  let : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure μ₃ := by
    dsimp [μ₃]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure μ₄ := by
    dsimp [μ₄]
    exact isProbabilityMeasure_standardComplexGaussianTail n
  let e₁ := sourceCoordinateReassocFirst n
  let e₂ := sourceCoordinateReassocSecond n
  let e₃ := sourceCoordinateReassocThird n
  have he₁ : Measure.map e₁
      ((μ₀.prod (μ₁.prod (μ₂.prod μ₃))).prod μ₄) =
      μ₀.prod ((μ₁.prod (μ₂.prod μ₃)).prod μ₄) := by
    exact Measure.prodAssoc_prod
  have he₂ : Measure.map e₂
      (μ₀.prod ((μ₁.prod (μ₂.prod μ₃)).prod μ₄)) =
      μ₀.prod (μ₁.prod ((μ₂.prod μ₃).prod μ₄)) := by
    rw [show (e₂ : (ℝ × ((ℝ × (ℝ × ℝ)) × Signal n)) →
        ℝ × (ℝ × ((ℝ × ℝ) × Signal n))) =
      Prod.map id MeasurableEquiv.prodAssoc by rfl]
    rw [← Measure.map_prod_map μ₀ ((μ₁.prod (μ₂.prod μ₃)).prod μ₄)
      measurable_id MeasurableEquiv.prodAssoc.measurable]
    simp only [Measure.map_id]
    rw [Measure.prodAssoc_prod]
  have he₃ : Measure.map e₃
      (μ₀.prod (μ₁.prod ((μ₂.prod μ₃).prod μ₄))) =
      μ₀.prod (μ₁.prod (μ₂.prod (μ₃.prod μ₄))) := by
    rw [show (e₃ : (ℝ × (ℝ × ((ℝ × ℝ) × Signal n))) →
        ℝ × (ℝ × (ℝ × (ℝ × Signal n)))) =
      Prod.map id (Prod.map id MeasurableEquiv.prodAssoc) by rfl]
    rw [← Measure.map_prod_map μ₀ (μ₁.prod ((μ₂.prod μ₃).prod μ₄))
      measurable_id (measurable_id.prodMap MeasurableEquiv.prodAssoc.measurable)]
    simp only [Measure.map_id]
    rw [← Measure.map_prod_map μ₁ ((μ₂.prod μ₃).prod μ₄)
      measurable_id MeasurableEquiv.prodAssoc.measurable]
    simp only [Measure.map_id]
    rw [Measure.prodAssoc_prod]
  change Measure.map (e₁.trans (e₂.trans e₃))
      ((μ₀.prod (μ₁.prod (μ₂.prod μ₃))).prod μ₄) =
      μ₀.prod (μ₁.prod (μ₂.prod (μ₃.prod μ₄)))
  rw [MeasurableEquiv.coe_trans e₁ (e₂.trans e₃)]
  rw [← Measure.map_map (e₂.trans e₃).measurable e₁.measurable]
  rw [MeasurableEquiv.coe_trans e₂ e₃]
  rw [← Measure.map_map e₃.measurable e₂.measurable, he₁, he₂, he₃]

/-- The deterministic scalar part of (3.21), with the two source phases
kept separate. -/
def sourceJacobianPhaseCenter (σ b g α : ℝ) : ℝ → ℝ :=
  fun β ↦ σ / 2 + b * Real.cos (β - α) - g * Real.sin (β - α)

theorem measurable_sourceJacobianPhaseCenter (σ b g α : ℝ) :
    Measurable (sourceJacobianPhaseCenter σ b g α) := by
  unfold sourceJacobianPhaseCenter
  fun_prop

/-- The literal tail-dominated small-ball event on the reassociated source
coordinates.  The cutoff makes off-cutoff radial sections empty. -/
def sourceTailDominatedCutoffSmallBallEvent {n : ℕ}
    (p q : Signal n) (σ b g B u : ℝ) :
    Set (ℝ × (ℝ × (ℝ × (ℝ × Signal n)))) :=
  {x | 0 < x.1 ∧ x.1 ≤ B ∧
    x.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧ x.2.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
    |sourceJacobianPhaseCenter σ b g x.2.2.1 x.2.2.2.1 +
      Real.sqrt (2 / x.1) *
        (star (Complex.exp ((-x.2.2.1 : ℂ) * Complex.I) • x.2.2.2.2) ⬝ᵥ
          (p + Complex.exp (((x.2.2.2.1 - x.2.2.1 : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u}

theorem measurableSet_sourceTailDominatedCutoffSmallBallEvent {n : ℕ}
    (p q : Signal n) (σ b g B u : ℝ) :
    MeasurableSet (sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) := by
  unfold sourceTailDominatedCutoffSmallBallEvent
  let fS : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) → ℝ := fun x ↦ x.1
  let fα : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) → ℝ := fun x ↦ x.2.2.1
  let fβ : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) → ℝ := fun x ↦ x.2.2.2.1
  have hfS : Measurable fS := by
    unfold fS
    fun_prop
  have hfα : Measurable fα := by
    unfold fα
    fun_prop
  have hfβ : Measurable fβ := by
    unfold fβ
    fun_prop
  let fJ : ℝ × (ℝ × (ℝ × (ℝ × Signal n))) → ℝ := fun x ↦
      |sourceJacobianPhaseCenter σ b g x.2.2.1 x.2.2.2.1 +
        Real.sqrt (2 / x.1) *
          (star (Complex.exp ((-x.2.2.1 : ℂ) * Complex.I) • x.2.2.2.2) ⬝ᵥ
            (p + Complex.exp (((x.2.2.2.1 - x.2.2.1 : ℝ) : ℂ) * Complex.I) • q)).re|
  have hfJ : Measurable fJ := by
    unfold fJ sourceJacobianPhaseCenter
    fun_prop
  change MeasurableSet
    (fS ⁻¹' Ioi 0 ∩ (fS ⁻¹' Iic B ∩
      (fα ⁻¹' Icc 0 (2 * Real.pi) ∩
        (fβ ⁻¹' Icc 0 (2 * Real.pi) ∩ fJ ⁻¹' Iic u))))
  exact (MeasurableSet.preimage measurableSet_Ioi hfS).inter
    ((MeasurableSet.preimage measurableSet_Iic hfS).inter
      ((MeasurableSet.preimage measurableSet_Icc hfα).inter
        ((MeasurableSet.preimage measurableSet_Icc hfβ).inter
          (MeasurableSet.preimage measurableSet_Iic hfJ))))

theorem tailConditionalSmallBall_bound_mono_radial
    (S B u t : ℝ) (_hS : 0 < S) (hSB : S ≤ B) (hu : 0 ≤ u) (ht : 0 < t) :
    ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt S / (Real.sqrt (2 * Real.pi) * t)) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt B / (Real.sqrt (2 * Real.pi) * t)) := by
  gcongr

/-- The tail-dominated small-ball event restricted to `0 < S ≤ B` has a
uniform bound after all of `ξ`, `α`, `β`, and `w` have been integrated. -/
theorem sourceCoordinateLawRight_tailDominatedCutoffSmallBall_le
    {n : ℕ} (η δ ε : ℝ) (p q : Signal n) (σ b g B u t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (_hB : 0 ≤ B) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    sourceCoordinateLawRight η δ ε n
        (sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt B / (Real.sqrt (2 * Real.pi) * t)) := by
  let μS := sourceRadialLaw η δ
  let μξ := sourceUniformInterval (-ε) ε
  let μα := sourceUniformInterval 0 (2 * Real.pi)
  let μβ := sourceUniformInterval 0 (2 * Real.pi)
  let ν := standardComplexGaussianTail n
  let : IsProbabilityMeasure μS := by
    dsimp [μS]
    exact isProbabilityMeasure_sourceRadialLaw hη0 hη1
  let : IsProbabilityMeasure μξ := by
    dsimp [μξ]
    exact isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure μα := by
    dsimp [μα]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure μβ := by
    dsimp [μβ]
    exact isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact isProbabilityMeasure_standardComplexGaussianTail n
  change (μS.prod (μξ.prod (μα.prod (μβ.prod ν))))
      (sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) ≤ _
  apply prod_measure_le_of_sections_le μS (μξ.prod (μα.prod (μβ.prod ν)))
    (measurableSet_sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) _
  intro S
  by_cases hS : 0 < S ∧ S ≤ B
  · have hSsection : MeasurableSet
        {x : ℝ × (ℝ × (ℝ × Signal n)) |
          (S, x) ∈ sourceTailDominatedCutoffSmallBallEvent p q σ b g B u} :=
      measurable_prodMk_left
        (measurableSet_sourceTailDominatedCutoffSmallBallEvent p q σ b g B u)
    apply prod_measure_le_of_sections_le μξ (μα.prod (μβ.prod ν)) hSsection _
    intro ξ
    have hξsection : MeasurableSet
        {x : ℝ × (ℝ × Signal n) |
          (ξ, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
            (S, y) ∈ sourceTailDominatedCutoffSmallBallEvent p q σ b g B u}} :=
      measurable_prodMk_left hSsection
    apply prod_measure_le_of_sections_le μα (μβ.prod ν) hξsection _
    intro α
    by_cases hα : α ∈ Icc 0 (2 * Real.pi)
    · have hbound :=
        sourceUniformInterval_prod_phaseNormalizedTailConditionalSmallBallOfCenter_le_rescaled
          p q α S (sourceJacobianPhaseCenter σ b g α) u t
          (measurable_sourceJacobianPhaseCenter σ b g α) hS.1 hu ht henergy
      have hmono := tailConditionalSmallBall_bound_mono_radial S B u t
        hS.1 hS.2 hu ht
      change (μβ.prod ν)
          {z | 0 < S ∧ S ≤ B ∧ α ∈ Icc 0 (2 * Real.pi) ∧
            z.1 ∈ Icc 0 (2 * Real.pi) ∧
            |sourceJacobianPhaseCenter σ b g α z.1 +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-α : ℂ) * Complex.I) • z.2) ⬝ᵥ
                  (p + Complex.exp (((z.1 - α : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u} ≤ _
      simp only [hS.1, hS.2, hα, true_and]
      exact hbound.trans hmono
    · have hempty :
        {z : ℝ × Signal n |
          (α, z) ∈ {x : ℝ × (ℝ × Signal n) |
            (ξ, x) ∈ {y : ℝ × (ℝ × (ℝ × Signal n)) |
              (S, y) ∈ sourceTailDominatedCutoffSmallBallEvent p q σ b g B u}}} = ∅ := by
          ext z
          change (0 < S ∧ S ≤ B ∧ α ∈ Icc 0 (2 * Real.pi) ∧
            z.1 ∈ Icc 0 (2 * Real.pi) ∧
            |sourceJacobianPhaseCenter σ b g α z.1 +
              Real.sqrt (2 / S) *
                (star (Complex.exp ((-α : ℂ) * Complex.I) • z.2) ⬝ᵥ
                  (p + Complex.exp (((z.1 - α : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u) ↔
            z ∈ (∅ : Set (ℝ × Signal n))
          simp [hα]
      rw [hempty, measure_empty]
      exact bot_le
  · have hempty :
      {x : ℝ × (ℝ × (ℝ × Signal n)) |
        (S, x) ∈ sourceTailDominatedCutoffSmallBallEvent p q σ b g B u} = ∅ := by
        ext x
        change (0 < S ∧ S ≤ B ∧ x.2.1 ∈ Icc 0 (2 * Real.pi) ∧
          x.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
          |sourceJacobianPhaseCenter σ b g x.2.1 x.2.2.1 +
            Real.sqrt (2 / S) *
              (star (Complex.exp ((-x.2.1 : ℂ) * Complex.I) • x.2.2.2) ⬝ᵥ
                (p + Complex.exp (((x.2.2.1 - x.2.1 : ℝ) : ℂ) * Complex.I) • q)).re| ≤ u) ↔
          x ∈ (∅ : Set (ℝ × (ℝ × (ℝ × Signal n))))
        by_cases hSpos : 0 < S
        · have hSupper : ¬ S ≤ B := by
            intro hSB
            exact hS ⟨hSpos, hSB⟩
          simp [hSpos, hSupper]
        · simp [hSpos]
    rw [hempty, measure_empty]
    exact bot_le

/-- Pull the cutoff event back through the explicit reassociation of the
repository's source-coordinate law. -/
def sourceTailDominatedCutoffSmallBallEventOnCoordinates {n : ℕ}
    (p q : Signal n) (σ b g B u : ℝ) : Set (SourcePlantedCoordinates n) :=
  (sourceCoordinateReassoc n) ⁻¹'
    sourceTailDominatedCutoffSmallBallEvent p q σ b g B u

/-- The cutoff estimate under the actual `sourceCoordinateLaw`.  It does
not yet bound the radial tail `S > B`; that term remains explicit. -/
theorem sourceCoordinateLaw_tailDominatedCutoffSmallBall_le
    {n : ℕ} (η δ ε : ℝ) (p q : Signal n) (σ b g B u t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hB : 0 ≤ B) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    sourceCoordinateLaw η δ ε n
        (sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u) ≤
      ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt B / (Real.sqrt (2 * Real.pi) * t)) := by
  have hmeas := measurableSet_sourceTailDominatedCutoffSmallBallEvent p q σ b g B u
  calc
    sourceCoordinateLaw η δ ε n
        (sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u) =
        Measure.map (sourceCoordinateReassoc n) (sourceCoordinateLaw η δ ε n)
          (sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) := by
      unfold sourceTailDominatedCutoffSmallBallEventOnCoordinates
      rw [Measure.map_apply (sourceCoordinateReassoc n).measurable hmeas]
    _ = sourceCoordinateLawRight η δ ε n
        (sourceTailDominatedCutoffSmallBallEvent p q σ b g B u) := by
      rw [sourceCoordinateLaw_map_reassoc η δ ε n hη0 hη1 hε]
    _ ≤ _ := sourceCoordinateLawRight_tailDominatedCutoffSmallBall_le
      η δ ε p q σ b g B u t hη0 hη1 hε hB hu ht henergy

end NLA.FR05
