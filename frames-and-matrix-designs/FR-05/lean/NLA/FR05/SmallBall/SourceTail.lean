import NLA.FR05.SmallBall.SourceTailConditional
import NLA.FR05.Densities.SourceRows
import NLA.FR05.Densities.SourceMarginals

/-! ## SourceTailBridge -/

section

/-
Exact source-coordinate interpretation of the cutoff tail small-ball event.

The conditional estimate is stated on reassociated product coordinates for
Tonelli's theorem.  This bridge identifies it with the literal row form in
equation (3.21) on the support of the planted source law.
-/


set_option autoImplicit false
noncomputable section

open Set

namespace NLA.FR05

/-- On the support where a source coordinate tuple represents a planted row,
the reassociated cutoff event is exactly the literal source Jacobian
small-ball event, with its radial and phase cutoffs displayed explicitly. -/
theorem mem_sourceTailDominatedCutoffSmallBallEventOnCoordinates_iff
    {n : ℕ} (x : SourcePlantedCoordinates n) (hS : 0 < x.1.1)
    (hxi : |x.1.2.1| ≤ 1) (p q : Signal n) (σ b g B u : ℝ) :
    x ∈ sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u ↔
      0 < x.1.1 ∧ x.1.1 ≤ B ∧
        x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) ∧
        |sourceRowJacobianForm (sourceCoordinatesToPlantedRow x hS hxi)
          σ b g p q| ≤ u := by
  rfl

end NLA.FR05

end
end

/-! ## SourceRowSmallBallEvent -/

section

/-
Shared literal source-row small-ball event and almost-sure source support.

Both branches of Lemma 3.6 are first proved on reassociated source
coordinates. This small module keeps the actual row event and the support
facts in a neutral location for their later combination.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- The literal row-form small-ball event, using the total source-to-row map.
Off source support that map is harmless, while on support it is the actual row. -/
def sourceRowJacobianSmallBallEvent {n : ℕ}
    (p q : Signal n) (sigma b g u : ℝ) : Set (SourcePlantedCoordinates n) :=
  {x | |sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault x)
    sigma b g p q| ≤ u}

/-- All source-coordinate support conditions used by the source-row bridges
hold almost surely under the actual product law. -/
theorem ae_sourceCoordinateLaw_fullSupport
    {eta delta epsilon : ℝ} (n : ℕ)
    (heta0 : 0 ≤ eta) (heta1 : eta < 1) (hepsilon : 0 < epsilon)
    (hdelta : 0 < delta) (hepsilon1 : epsilon ≤ 1) :
    ∀ᵐ x ∂sourceCoordinateLaw eta delta epsilon n,
      0 < x.1.1 ∧ |x.1.2.1| ≤ 1 ∧
        x.1.2.2.1 ∈ Icc 0 (2 * Real.pi) ∧
        x.1.2.2.2 ∈ Icc 0 (2 * Real.pi) := by
  let : IsProbabilityMeasure (sourceRadialLaw eta delta) :=
    isProbabilityMeasure_sourceRadialLaw heta0 heta1
  let : IsProbabilityMeasure (sourceUniformInterval (-epsilon) epsilon) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  rw [sourceCoordinateLaw, sourceScalarLaw]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceRadialLaw_Ici heta0 heta1] with S hS
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceUniformInterval_self (by linarith : -epsilon < epsilon)] with xi hxi
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceUniformInterval_self (by positivity : 0 < 2 * Real.pi)] with alpha halpha
  filter_upwards [ae_mem_sourceUniformInterval_self (by positivity : 0 < 2 * Real.pi)] with beta hbeta
  filter_upwards with w
  exact ⟨lt_of_lt_of_le hdelta hS, (abs_le.2 hxi).trans hepsilon1, halpha, hbeta⟩

end NLA.FR05

end

end

/-! ## SourceTailGlobal -/

section

/-
Global source-law wrapper for the tail-dominated small-ball estimate.

The conditional phase/Gaussian calculation is first restricted to a radial
cutoff.  This module puts that calculation back under the actual source law,
retaining the exact source radial upper-ray term (and then its manuscript
specialization) explicitly.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- Away from the radial upper ray, the literal row-form event is the cutoff
event on the almost-sure source support. -/
theorem ae_sourceRowJacobianSmallBall_subset_cutoff_union_radialTail
    {n : ℕ} (η δ ε : ℝ) (p q : Signal n) (σ b g B u : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    sourceRowJacobianSmallBallEvent p q σ b g u
      ≤ᵐ[sourceCoordinateLaw η δ ε n]
        Set.union (sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u)
          {x : SourcePlantedCoordinates n | B ≤ x.1.1} := by
  filter_upwards [ae_sourceCoordinateLaw_fullSupport n hη0 hη1 hε hδ hε1]
    with x hx
  intro hsmall
  by_cases hSB : x.1.1 ≤ B
  · left
    rw [mem_sourceTailDominatedCutoffSmallBallEventOnCoordinates_iff
      x hx.1 hx.2.1 p q σ b g B u]
    refine ⟨hx.1, hSB, hx.2.2.1, hx.2.2.2, ?_⟩
    have hsupp : 0 < x.1.1 ∧ |x.1.2.1| ≤ 1 := ⟨hx.1, hx.2.1⟩
    have hdefault : sourceCoordinatesToPlantedRowOrDefault x =
        sourceCoordinatesToPlantedRow x hx.1 hx.2.1 := by
      simp [sourceCoordinatesToPlantedRowOrDefault, hsupp]
    change |sourceRowJacobianForm (sourceCoordinatesToPlantedRowOrDefault x)
      σ b g p q| ≤ u at hsmall
    rw [hdefault] at hsmall
    exact hsmall
  · right
    exact le_of_not_ge hSB

/-- The tail-dominated source-row small-ball event is controlled by the
cutoff estimate plus the exact upper-ray probability of the source radial law.
The cutoff `B` and phase/Gaussian threshold `t` remain explicit. -/
theorem sourceCoordinateLaw_sourceRowJacobianSmallBall_le_add_radialTail
    {n : ℕ} (η δ ε : ℝ) (p q : Signal n) (σ b g B u t : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1)
    (hB : 0 ≤ B) (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    sourceCoordinateLaw η δ ε n
        (sourceRowJacobianSmallBallEvent p q σ b g u) ≤
      (ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt B / (Real.sqrt (2 * Real.pi) * t))) +
        sourceRadialLaw η δ (Ici B) := by
  have hsubset := ae_sourceRowJacobianSmallBall_subset_cutoff_union_radialTail
    (n := n) η δ ε p q σ b g B u hη0 hη1 hε hδ hε1
  calc
    sourceCoordinateLaw η δ ε n
        (sourceRowJacobianSmallBallEvent p q σ b g u) ≤
        sourceCoordinateLaw η δ ε n
          (Set.union (sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u)
            {x : SourcePlantedCoordinates n | B ≤ x.1.1}) :=
      measure_mono_ae hsubset
    _ ≤ sourceCoordinateLaw η δ ε n
          (sourceTailDominatedCutoffSmallBallEventOnCoordinates p q σ b g B u) +
        sourceCoordinateLaw η δ ε n {x | B ≤ x.1.1} :=
      measure_union_le _ _
    _ ≤ (ENNReal.ofReal (4 * t) +
          ENNReal.ofReal
            (2 * u * Real.sqrt B / (Real.sqrt (2 * Real.pi) * t))) +
          sourceRadialLaw η δ (Ici B) := by
      gcongr
      · exact sourceCoordinateLaw_tailDominatedCutoffSmallBall_le
          η δ ε p q σ b g B u t hη0 hη1 hε hB hu ht henergy
      · rw [sourceCoordinateLaw_radial_tail n hε]

/-- At the manuscript radial cutoff, the remaining source radial tail has
the checked exponential bound.  This is still only the tail-dominated branch
of Lemma 3.6: no bound for directions outside the displayed tail-energy
condition is asserted here. -/
theorem sourceCoordinateLaw_sourceM_sourceRowJacobianSmallBall_le
    {M n : ℕ} (hM : 1 ≤ M) (p q : Signal n) (σ b g u t : ℝ)
    (hu : 0 ≤ u) (ht : 0 < t)
    (henergy : (1 / 4 : ℝ) ≤ tailEnergy p + tailEnergy q) :
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent p q σ b g u) ≤
      (ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt (8 * (M : ℝ)) /
            (Real.sqrt (2 * Real.pi) * t))) +
        (25 : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-(4 * (M : ℝ)))) := by
  calc
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
        (sourceRowJacobianSmallBallEvent p q σ b g u) ≤
      (ENNReal.ofReal (4 * t) +
        ENNReal.ofReal
          (2 * u * Real.sqrt (8 * (M : ℝ)) /
            (Real.sqrt (2 * Real.pi) * t))) +
        sourceRadialLaw sourceEta (sourceDelta M) (Ici (8 * (M : ℝ))) :=
      sourceCoordinateLaw_sourceRowJacobianSmallBall_le_add_radialTail
        sourceEta (sourceDelta M) (sourceEpsilon M) p q σ b g (8 * (M : ℝ)) u t
        sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M hM)
        (sourceDelta_pos M hM) (sourceEpsilon_le_one M hM)
        (by positivity) hu ht henergy
    _ ≤ _ := by
      gcongr
      exact sourceRadialLaw_sourceM_apply_Ici_le hM

end NLA.FR05

end

end
