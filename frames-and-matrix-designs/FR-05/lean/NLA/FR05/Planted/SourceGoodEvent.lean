import NLA.FR05.Planted.DerivativeNorm
import NLA.FR05.Densities.SourceMarginals
import NLA.FR05.Densities.SourceRows

/-!
# Source good events and finite row-energy estimates

The sections develop `FiniteRowEnergy`, `SourceGoodEvent`.
-/

set_option autoImplicit false
noncomputable section

namespace NLA.FR05

section FiniteRowEnergy

/-
Finite-row tail lift for the source-coordinate energy event.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

theorem iidSourceCoordinateLawAt_radial_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (M : ℝ) ≤ (p i).1.1} ≤
      25 * Real.exp (-(4 * (M : ℝ))) := by
  let μ0 : Measure (SourcePlantedCoordinates n) :=
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
  let : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_sourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) n
  have hpres : MeasurePreserving (Function.eval i)
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) μ0 :=
    measurePreserving_eval _ i
  let s : Set (SourcePlantedCoordinates n) := {p | 8 * (M : ℝ) ≤ p.1.1}
  have hs : MeasurableSet s := measurableSet_Ici.preimage (measurable_fst.comp measurable_fst)
  refine (hpres.measureReal_preimage hs.nullMeasurableSet).le.trans ?_
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  exact sourceCoordinateLaw_sourceM_radial_tail n hM

theorem iidSourceCoordinateLawAt_tail_energy_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (n : ℝ) ≤ signalEnergy (p i).2} ≤
      Real.exp (-3 * (n : ℝ)) := by
  let μ0 : Measure (SourcePlantedCoordinates n) :=
    sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) n
  let : IsProbabilityMeasure μ0 :=
    isProbabilityMeasure_sourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) n
  have hpres : MeasurePreserving (Function.eval i)
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) μ0 :=
    measurePreserving_eval _ i
  let s : Set (SourcePlantedCoordinates n) :=
    {p | 8 * (n : ℝ) ≤ signalEnergy p.2}
  have hs : MeasurableSet s :=
    measurableSet_Ici.preimage (measurable_signalEnergy.comp measurable_snd)
  refine (hpres.measureReal_preimage hs.nullMeasurableSet).le.trans ?_
  exact ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _)
    (sourceCoordinateLaw_tail_energy_tail n sourceEta_pos.le
      sourceEta_lt_one (sourceEpsilon_pos M hM))

theorem iidSourceCoordinateLawAt_tail_energy_tail_at_M_real
    {M m n : ℕ} (hM : 1 ≤ M) (hnM : n ≤ M) (i : Fin m) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | 8 * (M : ℝ) ≤ signalEnergy (p i).2} ≤
      Real.exp (-3 * (n : ℝ)) := by
  let : IsProbabilityMeasure
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) :=
    isProbabilityMeasure_iidSourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) m n
  apply le_trans (measureReal_mono ?_)
    (iidSourceCoordinateLawAt_tail_energy_tail_real hM i)
  intro p hp
  exact (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hnM) (by norm_num : (0 : ℝ) ≤ 8)).trans hp

/-- The source's coordinatewise tail estimates lift to the finite-row event
in (3.22), before converting source coordinates to checked planted rows. -/
theorem iidSourceCoordinateLawAt_row_energy_max_tail_real
    {M m n : ℕ} (hM : 1 ≤ M) (hnM : n ≤ M) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | ∃ i, 16 * (M : ℝ) ≤ (p i).1.1 + signalEnergy (p i).2} ≤
      m * (25 * Real.exp (-(4 * (M : ℝ))) + Real.exp (-3 * (n : ℝ))) := by
  let : IsProbabilityMeasure
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) :=
    isProbabilityMeasure_iidSourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M hM) m n
  exact row_energy_max_tail_of_component_tails
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n)
    m (M : ℝ) (25 * Real.exp (-(4 * (M : ℝ))))
    (Real.exp (-3 * (n : ℝ)))
    (fun i p => (p i).1.1) (fun i p => signalEnergy (p i).2)
    (fun i => iidSourceCoordinateLawAt_radial_tail_real hM i)
    (fun i => iidSourceCoordinateLawAt_tail_energy_tail_at_M_real hM hnM i)

end FiniteRowEnergy

section SourceGoodEvent

/-
Pointwise good-event consequences for the actual source-coordinate model.

This bridges the finite-row radial/tail-energy event to the deterministic
derivative estimate, without replacing the source distribution by an
auxiliary row model.
-/

open MeasureTheory ProbabilityTheory Set

/-- The rowwise radial, support, and energy conditions used for the
source good event. -/
def SourceCoordinateRowGood (M : ℕ) {n : ℕ}
    (p : SourcePlantedCoordinates n) : Prop :=
  sourceDelta M ≤ p.1.1 ∧ |p.1.2.1| ≤ 1 ∧
    p.1.1 + signalEnergy p.2 ≤ 16 * (M : ℝ)

/-- The finite sample version of the source good event. -/
def SourceCoordinateSampleGood (M : ℕ) {m n : ℕ}
    (p : Fin m → SourcePlantedCoordinates n) : Prop :=
  ∀ i, SourceCoordinateRowGood M (p i)

/-- The radial and imbalance support conditions hold simultaneously for
every coordinate of a finite iid source sample. -/
theorem ae_iidSourceCoordinateLaw_support
    {η δ ε : ℝ} {m n : ℕ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    ∀ᵐ p ∂iidSourceCoordinateLaw η δ ε m n,
      ∀ i, δ ≤ (p i).1.1 ∧ |(p i).1.2.1| ≤ ε := by
  rw [ae_all_iff]
  intro i
  let μ : Measure (SourcePlantedCoordinates n) := sourceCoordinateLaw η δ ε n
  let _ : IsProbabilityMeasure μ :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  have hpres : MeasurePreserving (Function.eval i)
      (iidSourceCoordinateLaw η δ ε m n) μ :=
    measurePreserving_eval _ i
  exact hpres.quasiMeasurePreserving.ae (ae_sourceCoordinateLaw_support n hη0 hη1 hε)

/-- Except on the explicit finite-row energy tail event, every source sample
lies in the good event needed by the derivative argument. -/
theorem ae_not_sourceCoordinateSampleGood_le_rowEnergyTail
    {M m n : ℕ} (hM : 2 ≤ M) :
    {p : Fin m → SourcePlantedCoordinates n | ¬ SourceCoordinateSampleGood M p}
      ≤ᵐ[iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n]
    {p | ∃ i, 16 * (M : ℝ) ≤ (p i).1.1 + signalEnergy (p i).2} := by
  have hsupp := ae_iidSourceCoordinateLaw_support
    (η := sourceEta) (δ := sourceDelta M) (ε := sourceEpsilon M)
    (m := m) (n := n) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M (by lia))
  filter_upwards [hsupp] with p hp
  change ¬ SourceCoordinateSampleGood M p →
    ∃ i, 16 * (M : ℝ) ≤ (p i).1.1 + signalEnergy (p i).2
  intro hnot
  by_contra htail
  apply hnot
  intro i
  refine ⟨(hp i).1, (hp i).2.trans (sourceEpsilon_le_one M (by lia)), ?_⟩
  exact le_of_lt (lt_of_not_ge fun henergy => htail ⟨i, henergy⟩)

/-- The source's explicit finite-row tail estimate controls the probability
that the derivative good event fails. -/
theorem iidSourceCoordinateLawAt_not_sourceCoordinateSampleGood_real_le
    {M m n : ℕ} (hM : 2 ≤ M) (hnM : n ≤ M) :
    (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n).real
        {p | ¬ SourceCoordinateSampleGood M p} ≤
      m * (25 * Real.exp (-(4 * (M : ℝ))) + Real.exp (-3 * (n : ℝ))) := by
  let _ : IsProbabilityMeasure
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M) m n) :=
    isProbabilityMeasure_iidSourceCoordinateLaw sourceEta_pos.le sourceEta_lt_one
      (sourceEpsilon_pos M (by lia)) m n
  have hmeasure := ae_not_sourceCoordinateSampleGood_le_rowEnergyTail
    (m := m) (n := n) hM
  grw [Measure.real_def, measure_mono_ae hmeasure]
  · exact iidSourceCoordinateLawAt_row_energy_max_tail_real (by lia) hnM
  · exact measure_ne_top _ _

/-- The actual iid source law satisfies the seed-residual estimate in
equation (3.24) almost surely; this is the direct source-coordinate version
of `F^ε(0) = ξ`. -/
theorem ae_iidSourceCoordinateLawAt_plantedEquationMap_zero_euclideanNorm_le
    {M m : ℕ} (hM : 2 ≤ M) :
    ∀ᵐ sample ∂iidSourceCoordinateLaw sourceEta (sourceDelta M)
      (sourceEpsilon M) m (sourceTailDimension M),
      realEuclideanNorm (plantedEquationMap (sourceRowsFromCoordinates sample) 0) ≤
        sourceEpsilon M * Real.sqrt m := by
  have hsupp := ae_iidSourceCoordinateLaw_support
    (η := sourceEta) (δ := sourceDelta M) (ε := sourceEpsilon M)
    (m := m) (n := sourceTailDimension M)
    sourceEta_pos.le sourceEta_lt_one (sourceEpsilon_pos M (by lia))
  filter_upwards [hsupp] with sample hsample
  apply plantedEquationMap_zero_euclideanNorm_le
  · exact (sourceEpsilon_pos M (by lia)).le
  · intro i
    have hpos : 0 < (sample i).1.1 :=
      lt_of_lt_of_le (sourceDelta_pos M (by lia)) (hsample i).1
    have hxi : |(sample i).1.2.1| ≤ 1 :=
      (hsample i).2.trans (sourceEpsilon_le_one M (by lia))
    have hsupport : 0 < (sample i).1.1 ∧ |(sample i).1.2.1| ≤ 1 :=
      ⟨hpos, hxi⟩
    change |(sourceCoordinatesToPlantedRowOrDefault (sample i)).imbalance| ≤
      sourceEpsilon M
    simpa [sourceCoordinatesToPlantedRowOrDefault, sourceCoordinatesToPlantedRow,
      hsupport] using (hsample i).2

/-- On the concrete support event, the total source-to-row map is the
intended planted row, rather than its off-support default. -/
theorem sourceCoordinatesToPlantedRowOrDefault_eq_of_good
    {M n : ℕ} (hM : 2 ≤ M) (p : SourcePlantedCoordinates n)
    (hgood : SourceCoordinateRowGood M p) :
    sourceCoordinatesToPlantedRowOrDefault p =
      sourceCoordinatesToPlantedRow p
        (lt_of_lt_of_le (sourceDelta_pos M (by lia)) hgood.1) hgood.2.1 := by
  have hs : 0 < p.1.1 ∧ |p.1.2.1| ≤ 1 :=
    ⟨lt_of_lt_of_le (sourceDelta_pos M (by lia)) hgood.1, hgood.2.1⟩
  simp [sourceCoordinatesToPlantedRowOrDefault, hs]

/-- The coordinate good event gives the source-scale uniform row constant
for the actual planted row. -/
theorem plantedRowSupEnergy_sourceCoordinatesToPlantedRowOrDefault_le
    {M : ℕ} (hM : 2 ≤ M)
    (p : SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateRowGood M p) :
    plantedRowSupEnergy (sourceCoordinatesToPlantedRowOrDefault p) ≤
      16 * (M : ℝ) ^ 5 := by
  rw [sourceCoordinatesToPlantedRowOrDefault_eq_of_good hM p hgood]
  apply plantedRowSupEnergy_le_source_bound hM
  · exact hgood.1
  · simpa [sourceCoordinatesToPlantedRow, signalEnergy] using hgood.2.2

/-- The checked rowwise derivative variation is therefore polynomially
bounded on the actual source-coordinate good event. -/
theorem abs_plantedEquationDirectional_sub_linear_source_good_le
    {M : ℕ} (hM : 2 ≤ M)
    (p : SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateRowGood M p)
    (s σ : ℝ) (b c : ℂ)
    (z t u v : Signal (sourceTailDimension M))
    {R S : ℝ} (hR : 0 ≤ R) (hbase : factorDirectionSup s b z t ≤ R)
    (hdirection : factorDirectionSup σ c u v ≤ S) :
    |plantedEquationDirectional (sourceCoordinatesToPlantedRowOrDefault p)
        s b z t σ c u v -
        plantedEquationLinear (sourceCoordinatesToPlantedRowOrDefault p)
          σ c u v| ≤
      32 * (M : ℝ) ^ 5 * R * S := by
  calc
    |plantedEquationDirectional (sourceCoordinatesToPlantedRowOrDefault p)
        s b z t σ c u v -
        plantedEquationLinear (sourceCoordinatesToPlantedRowOrDefault p)
          σ c u v| ≤
        2 * plantedRowSupEnergy (sourceCoordinatesToPlantedRowOrDefault p) * R * S :=
      abs_plantedEquationDirectional_sub_linear_le_of_sup_le
        (sourceCoordinatesToPlantedRowOrDefault p) s σ b c z t u v
        hR hbase hdirection
    _ ≤ 32 * (M : ℝ) ^ 5 * R * S := by
      have hrow :=
        plantedRowSupEnergy_sourceCoordinatesToPlantedRowOrDefault_le hM p hgood
      have hS : 0 ≤ S :=
        le_trans (factorDirectionSup_nonneg σ c u v) hdirection
      calc
        2 * plantedRowSupEnergy (sourceCoordinatesToPlantedRowOrDefault p) * R * S ≤
            2 * (16 * (M : ℝ) ^ 5) * R * S := by
          gcongr
        _ = 32 * (M : ℝ) ^ 5 * R * S := by ring

/-- The derivative estimate holds simultaneously for every row on the
finite source-coordinate good event. -/
theorem abs_plantedEquationDirectional_sub_linear_source_sample_good_le
    {M m : ℕ} (hM : 2 ≤ M)
    (sample : Fin m → SourcePlantedCoordinates (sourceTailDimension M))
    (hgood : SourceCoordinateSampleGood M sample) (i : Fin m)
    (s σ : ℝ) (b c : ℂ)
    (z t u v : Signal (sourceTailDimension M))
    {R S : ℝ} (hR : 0 ≤ R) (hbase : factorDirectionSup s b z t ≤ R)
    (hdirection : factorDirectionSup σ c u v ≤ S) :
    |plantedEquationDirectional (sourceRowsFromCoordinates sample i)
        s b z t σ c u v -
        plantedEquationLinear (sourceRowsFromCoordinates sample i)
          σ c u v| ≤
      32 * (M : ℝ) ^ 5 * R * S := by
  exact abs_plantedEquationDirectional_sub_linear_source_good_le hM
    (sample i) (hgood i) s σ b c z t u v hR hbase hdirection

end SourceGoodEvent

end NLA.FR05
