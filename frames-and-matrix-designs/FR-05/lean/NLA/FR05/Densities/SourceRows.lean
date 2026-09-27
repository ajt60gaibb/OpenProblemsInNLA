import NLA.FR05.Densities.PlantedLaw

/-! ## SourceRowBridge -/

section

/-
The deterministic bridge from the source-coordinate representation to the
checked `PlantedRow` interface.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace NLA.FR05

theorem ae_mem_sourceRadialLaw_Ici {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    ∀ᵐ S ∂sourceRadialLaw η δ, S ∈ Ici δ := by
  let : IsProbabilityMeasure (sourceRadialLaw η δ) :=
    isProbabilityMeasure_sourceRadialLaw hη0 hη1
  change Ici δ ∈ ae (sourceRadialLaw η δ)
  rw [mem_ae_iff_prob_eq_one measurableSet_Ici]
  exact sourceRadialLaw_apply_Ici hη0 hη1

theorem ae_mem_sourceUniformInterval_self {a b : ℝ} (hab : a < b) :
    ∀ᵐ x ∂sourceUniformInterval a b, x ∈ Icc a b := by
  let : IsProbabilityMeasure (sourceUniformInterval a b) :=
    isProbabilityMeasure_sourceUniformInterval hab
  change Icc a b ∈ ae (sourceUniformInterval a b)
  rw [mem_ae_iff_prob_eq_one measurableSet_Icc]
  exact sourceUniformInterval_apply_self hab

/-- Under the scalar source law, both defining scalar support conditions hold
almost surely. -/
theorem ae_sourceScalarLaw_support {η δ ε : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    ∀ᵐ q ∂sourceScalarLaw η δ ε, δ ≤ q.1 ∧ |q.2.1| ≤ ε := by
  let : IsProbabilityMeasure (sourceRadialLaw η δ) :=
    isProbabilityMeasure_sourceRadialLaw hη0 hη1
  let : IsProbabilityMeasure (sourceUniformInterval (-ε) ε) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  let : IsProbabilityMeasure
      ((sourceUniformInterval 0 (2 * Real.pi)).prod
        (sourceUniformInterval 0 (2 * Real.pi))) :=
    Measure.prod.instIsProbabilityMeasure _ _
  let : IsProbabilityMeasure
      ((sourceUniformInterval (-ε) ε).prod
        ((sourceUniformInterval 0 (2 * Real.pi)).prod
          (sourceUniformInterval 0 (2 * Real.pi)))) :=
    Measure.prod.instIsProbabilityMeasure _ _
  rw [sourceScalarLaw]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceRadialLaw_Ici hη0 hη1] with S hS
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_mem_sourceUniformInterval_self (by linarith : -ε < ε)] with ξ hξ
  filter_upwards with phases
  exact ⟨hS, abs_le.2 hξ⟩

/-- The corresponding support fact after adjoining the independent Gaussian
tail coordinates. -/
theorem ae_sourceCoordinateLaw_support {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    ∀ᵐ p ∂sourceCoordinateLaw η δ ε n,
      δ ≤ p.1.1 ∧ |p.1.2.1| ≤ ε := by
  let : IsProbabilityMeasure (sourceScalarLaw η δ ε) :=
    isProbabilityMeasure_sourceScalarLaw hη0 hη1 hε
  rw [sourceCoordinateLaw]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [ae_sourceScalarLaw_support hη0 hη1 hε] with q hq
  filter_upwards with w
  exact hq

/-- If the radial cutoff is positive and the imbalance interval lies in
`[-1,1]`, source coordinates define a checked planted row almost surely. -/
theorem ae_sourceCoordinateLaw_plantedSupport {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    ∀ᵐ p ∂sourceCoordinateLaw η δ ε n,
      0 < p.1.1 ∧ |p.1.2.1| ≤ 1 := by
  filter_upwards [ae_sourceCoordinateLaw_support n hη0 hη1 hε] with p hp
  exact ⟨lt_of_lt_of_le hδ hp.1, hp.2.trans hε1⟩

/-- Turn source coordinates into the checked deterministic row once the two
support inequalities have been established. -/
def sourceCoordinatesToPlantedRow {n : ℕ} (p : SourcePlantedCoordinates n)
    (hS : 0 < p.1.1) (hξ : |p.1.2.1| ≤ 1) : PlantedRow n :=
  { radial := p.1.1
    imbalance := p.1.2.1
    phaseOne := p.1.2.2.1
    phaseTwo := p.1.2.2.2
    tail := p.2
    radial_pos := hS
    imbalance_le_one := hξ }

theorem sourcePlantedColumn_eq_plantedColumn_of_support {n : ℕ}
    (p : SourcePlantedCoordinates n) (hS : 0 < p.1.1) (hξ : |p.1.2.1| ≤ 1) :
    sourcePlantedColumn p =
      plantedColumn (sourceCoordinatesToPlantedRow p hS hξ) := by
  rfl

/-- A total version of the source-to-row map.  Off the support of the source
law it uses the harmless deterministic row `(1,0,0,0,0)`. -/
def sourceCoordinatesToPlantedRowOrDefault {n : ℕ}
    (p : SourcePlantedCoordinates n) : PlantedRow n :=
  if h : 0 < p.1.1 ∧ |p.1.2.1| ≤ 1 then
    sourceCoordinatesToPlantedRow p h.1 h.2
  else
    { radial := 1
      imbalance := 0
      phaseOne := 0
      phaseTwo := 0
      tail := 0
      radial_pos := zero_lt_one
      imbalance_le_one := by norm_num }

theorem sourcePlantedColumn_eq_plantedColumnOrDefault_of_support {n : ℕ}
    (p : SourcePlantedCoordinates n) (hS : 0 < p.1.1) (hξ : |p.1.2.1| ≤ 1) :
    sourcePlantedColumn p =
      plantedColumn (sourceCoordinatesToPlantedRowOrDefault p) := by
  have h : 0 < p.1.1 ∧ |p.1.2.1| ≤ 1 := ⟨hS, hξ⟩
  simp [sourceCoordinatesToPlantedRowOrDefault, sourceCoordinatesToPlantedRow,
    sourcePlantedColumn, plantedColumn, h]

/-- The raw source formula agrees almost surely with `plantedColumn` applied
to a total map into the deterministic checked interface. -/
theorem ae_sourcePlantedColumn_eq_plantedColumnOrDefault
    {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    sourcePlantedColumn =ᵐ[sourceCoordinateLaw η δ ε n]
      fun p => plantedColumn (sourceCoordinatesToPlantedRowOrDefault p) := by
  filter_upwards [ae_sourceCoordinateLaw_plantedSupport n hη0 hη1 hε hδ hε1]
    with p hp
  exact sourcePlantedColumn_eq_plantedColumnOrDefault_of_support p hp.1 hp.2

/-- The source imbalance width `M⁻⁵⁰` is contained in the deterministic
row domain `[-1,1]`. -/
theorem sourceEpsilon_le_one (M : ℕ) (hM : 1 ≤ M) : sourceEpsilon M ≤ 1 := by
  unfold sourceEpsilon
  have hMreal : 1 ≤ (M : ℝ) := by
    exact_mod_cast hM
  have hpow : 1 ≤ (M : ℝ) ^ 50 := one_le_pow₀ hMreal
  exact inv_le_one_of_one_le₀ hpow

/-- At the manuscript parameters, the source column formula is almost surely
a column generated by a `PlantedRow`. -/
theorem ae_sourcePlantedColumn_eq_plantedColumnOrDefaultAt
    {M : ℕ} (hM : 1 ≤ M) :
    sourcePlantedColumn =ᵐ[
      sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceTailDimension M)]
      fun p => plantedColumn (sourceCoordinatesToPlantedRowOrDefault p) := by
  exact ae_sourcePlantedColumn_eq_plantedColumnOrDefault
    (sourceTailDimension M) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M hM) (sourceDelta_pos M hM)
    (sourceEpsilon_le_one M hM)

/-- The source column law is unchanged if one passes through the checked
`PlantedRow` interface with its defaulted off-support representative. -/
theorem sourcePlantedColumnLaw_eq_viaPlantedRow
    {η δ ε : ℝ} (n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    sourcePlantedColumnLaw η δ ε n =
      (sourceCoordinateLaw η δ ε n).map
        (fun p => plantedColumn (sourceCoordinatesToPlantedRowOrDefault p)) := by
  unfold sourcePlantedColumnLaw
  exact Measure.map_congr
    (ae_sourcePlantedColumn_eq_plantedColumnOrDefault n hη0 hη1 hε hδ hε1)

theorem sourcePlantedColumnLawAt_eq_viaPlantedRow
    {M : ℕ} (hM : 1 ≤ M) :
    sourcePlantedColumnLaw sourceEta (sourceDelta M) (sourceEpsilon M)
      (sourceTailDimension M) =
      (sourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceTailDimension M)).map
        (fun p => plantedColumn (sourceCoordinatesToPlantedRowOrDefault p)) := by
  exact sourcePlantedColumnLaw_eq_viaPlantedRow
    (sourceTailDimension M) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M hM) (sourceDelta_pos M hM)
    (sourceEpsilon_le_one M hM)

/-- IID source coordinates before applying the planted formula coordinatewise. -/
def iidSourceCoordinateLaw (η δ ε : ℝ) (m n : ℕ) :
    Measure (Fin m → SourcePlantedCoordinates n) :=
  Measure.pi (fun _ ↦ sourceCoordinateLaw η δ ε n)

theorem isProbabilityMeasure_iidSourceCoordinateLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) (m n : ℕ) :
    IsProbabilityMeasure (iidSourceCoordinateLaw η δ ε m n) := by
  exact @MeasureTheory.Measure.pi.instIsProbabilityMeasure
    (Fin m) (fun _ ↦ SourcePlantedCoordinates n) _ _
    (fun _ ↦ sourceCoordinateLaw η δ ε n)
    (fun _ ↦ isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n)

/-- Apply the raw formula to every independent source-coordinate sample. -/
def sourceColumnsFromCoordinates {m n : ℕ}
    (p : Fin m → SourcePlantedCoordinates n) : Fin m → Signal (n + 2) :=
  fun i ↦ sourcePlantedColumn (p i)

theorem measurable_sourceColumnsFromCoordinates {m n : ℕ} :
    Measurable (sourceColumnsFromCoordinates (m := m) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_sourcePlantedColumn.comp (measurable_pi_apply i)

def sourceFrameFromCoordinates {m n : ℕ}
    (p : Fin m → SourcePlantedCoordinates n) : Frame m (n + 2) :=
  frameFromPlantedColumns (sourceColumnsFromCoordinates p)

/-- The checked deterministic-row representation of all coordinate samples. -/
def sourceRowsFromCoordinates {m n : ℕ}
    (p : Fin m → SourcePlantedCoordinates n) : Fin m → PlantedRow n :=
  fun i ↦ sourceCoordinatesToPlantedRowOrDefault (p i)

/-- The iid column law is the pushforward of the iid coordinate law. -/
theorem iidSourcePlantedColumnLaw_eq_coordinatesMap
    {η δ ε : ℝ} (m n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    iidSourcePlantedColumnLaw η δ ε m n =
      (iidSourceCoordinateLaw η δ ε m n).map sourceColumnsFromCoordinates := by
  let : IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  let : IsProbabilityMeasure (sourcePlantedColumnLaw η δ ε n) :=
    isProbabilityMeasure_sourcePlantedColumnLaw hη0 hη1 hε n
  unfold iidSourcePlantedColumnLaw iidSourceCoordinateLaw sourcePlantedColumnLaw
  symm
  exact Measure.pi_map_pi fun _ => measurable_sourcePlantedColumn.aemeasurable

/-- Likewise, the iid source frame law is the direct pushforward of iid
source coordinates. -/
theorem iidSourcePlantedFrameLaw_eq_coordinatesMap
    {η δ ε : ℝ} (m n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    iidSourcePlantedFrameLaw η δ ε m n =
      (iidSourceCoordinateLaw η δ ε m n).map sourceFrameFromCoordinates := by
  unfold iidSourcePlantedFrameLaw
  rw [iidSourcePlantedColumnLaw_eq_coordinatesMap m n hη0 hη1 hε]
  rw [Measure.map_map measurable_frameFromPlantedColumns
    measurable_sourceColumnsFromCoordinates]
  rfl

/-- The whole independently planted frame agrees almost surely with the
checked `plantedFrame` construction. -/
theorem ae_sourceFrameFromCoordinates_eq_plantedFrame
    {η δ ε : ℝ} (m n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    sourceFrameFromCoordinates =ᵐ[iidSourceCoordinateLaw η δ ε m n]
      fun p => plantedFrame (sourceRowsFromCoordinates p) := by
  let : IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  have hcolumns :
      (fun p : Fin m → SourcePlantedCoordinates n =>
        fun i => sourcePlantedColumn (p i)) =ᵐ[
          iidSourceCoordinateLaw η δ ε m n]
        fun p i => plantedColumn (sourceCoordinatesToPlantedRowOrDefault (p i)) := by
    unfold iidSourceCoordinateLaw
    exact Measure.ae_eq_pi fun _ =>
      ae_sourcePlantedColumn_eq_plantedColumnOrDefault n hη0 hη1 hε hδ hε1
  filter_upwards [hcolumns] with p hp
  funext i
  exact congrArg star (congrFun hp i)

theorem ae_sourceFrameFromCoordinates_eq_plantedFrameAt
    {M : ℕ} (hM : 1 ≤ M) :
    sourceFrameFromCoordinates =ᵐ[
      iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)]
      fun p => plantedFrame (sourceRowsFromCoordinates p) := by
  exact ae_sourceFrameFromCoordinates_eq_plantedFrame
    (sourceRowCount M) (sourceTailDimension M) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M hM) (sourceDelta_pos M hM)
    (sourceEpsilon_le_one M hM)

/-- The actual iid planted-frame law factors through the checked deterministic
`plantedFrame` construction, up to equality of measures. -/
theorem iidSourcePlantedFrameLaw_eq_viaPlantedRows
    {η δ ε : ℝ} (m n : ℕ)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    (hδ : 0 < δ) (hε1 : ε ≤ 1) :
    iidSourcePlantedFrameLaw η δ ε m n =
      (iidSourceCoordinateLaw η δ ε m n).map
        (fun p => plantedFrame (sourceRowsFromCoordinates p)) := by
  calc
    iidSourcePlantedFrameLaw η δ ε m n =
        (iidSourceCoordinateLaw η δ ε m n).map sourceFrameFromCoordinates :=
      iidSourcePlantedFrameLaw_eq_coordinatesMap m n hη0 hη1 hε
    _ = (iidSourceCoordinateLaw η δ ε m n).map
        (fun p => plantedFrame (sourceRowsFromCoordinates p)) :=
      Measure.map_congr
        (ae_sourceFrameFromCoordinates_eq_plantedFrame m n hη0 hη1 hε hδ hε1)

theorem sourcePlantedFrameLawAt_eq_viaPlantedRows
    {M : ℕ} (hM : 1 ≤ M) :
    sourcePlantedFrameLawAt M =
      (iidSourceCoordinateLaw sourceEta (sourceDelta M) (sourceEpsilon M)
        (sourceRowCount M) (sourceTailDimension M)).map
        (fun p => plantedFrame (sourceRowsFromCoordinates p)) := by
  unfold sourcePlantedFrameLawAt
  exact iidSourcePlantedFrameLaw_eq_viaPlantedRows
    (sourceRowCount M) (sourceTailDimension M) sourceEta_pos.le sourceEta_lt_one
    (sourceEpsilon_pos M hM) (sourceDelta_pos M hM)
    (sourceEpsilon_le_one M hM)

end NLA.FR05

end
end

/-! ## IidRowSplit -/

section

/-
Measurable product decomposition of a finite iid source-coordinate sample.

This is the conditioning interface needed in the row-to-span part of
Lemma 3.7: one selected row is separated from all other rows while preserving
the actual source-coordinate product law.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLA.FR05

/-- Split a sample of `m + 1` source rows into row `i` and the remaining rows,
with the latter indexed through `Fin.succAbove i`. -/
noncomputable def iidSourceCoordinateSplit
    (m n : ℕ) (i : Fin (m + 1)) :
    (Fin (m + 1) → SourcePlantedCoordinates n) ≃ᵐ
      SourcePlantedCoordinates n × (Fin m → SourcePlantedCoordinates n) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => SourcePlantedCoordinates n) i

theorem iidSourceCoordinateSplit_fst_apply
    {m n : ℕ} (i : Fin (m + 1))
    (sample : Fin (m + 1) → SourcePlantedCoordinates n) :
    (iidSourceCoordinateSplit m n i sample).1 = sample i := rfl

theorem iidSourceCoordinateSplit_snd_apply
    {m n : ℕ} (i : Fin (m + 1))
    (sample : Fin (m + 1) → SourcePlantedCoordinates n) (j : Fin m) :
    (iidSourceCoordinateSplit m n i sample).2 j = sample (i.succAbove j) := rfl

/-- The source iid law is preserved by separating any one row from the other
`m` rows.  This is an exact finite-product identity, not an independence
heuristic. -/
theorem measurePreserving_iidSourceCoordinateSplit
    {η δ ε : ℝ} (m n : ℕ) (i : Fin (m + 1))
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    MeasurePreserving (iidSourceCoordinateSplit m n i)
      (iidSourceCoordinateLaw η δ ε (m + 1) n)
      ((sourceCoordinateLaw η δ ε n).prod (iidSourceCoordinateLaw η δ ε m n)) := by
  let _ : IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  change MeasurePreserving
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (m + 1) => SourcePlantedCoordinates n) i)
    (Measure.pi (fun _ : Fin (m + 1) => sourceCoordinateLaw η δ ε n))
    ((sourceCoordinateLaw η δ ε n).prod
      (Measure.pi (fun _ : Fin m => sourceCoordinateLaw η δ ε n)))
  exact measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => sourceCoordinateLaw η δ ε n) i

end NLA.FR05

end

end
