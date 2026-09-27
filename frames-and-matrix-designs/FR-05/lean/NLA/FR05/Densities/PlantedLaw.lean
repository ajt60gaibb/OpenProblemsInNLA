import NLA.FR05.SourceParameters
import NLA.FR05.Probability
import NLA.FR05.Gaussian.GaussianTail
import Mathlib.Probability.Distributions.Exponential
import NLA.FR05.Measure.ProductSections

/-! ## PlantedLaw -/

section

/-
The source-faithful planted row law from §3.1 and equation (3.18) of the
frozen FR-05 manuscript.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace NLA.FR05

/-- The unconditioned mixture with density
`((1 - η) + η * s) * exp (-s)` on the nonnegative real line. -/
def sourceRadialBase (η : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - η) • expMeasure 1 +
    ENNReal.ofReal η • gammaMeasure 2 1

theorem isProbabilityMeasure_sourceRadialBase {η : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    IsProbabilityMeasure (sourceRadialBase η) := by
  constructor
  have hexp : expMeasure (1 : ℝ) Set.univ = 1 :=
    (isProbabilityMeasure_expMeasure zero_lt_one).measure_univ
  have hgamma : gammaMeasure (2 : ℝ) 1 Set.univ = 1 :=
    (isProbabilityMeasure_gammaMeasure (by norm_num) zero_lt_one).measure_univ
  rw [sourceRadialBase, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    hexp, hgamma]
  simp only [smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hη1) hη0]
  norm_num

/-- The exponential component gives positive mass to every upper ray. -/
theorem expMeasure_Ici_ne_zero (δ : ℝ) : expMeasure 1 (Ici δ) ≠ 0 := by
  let : IsProbabilityMeasure (expMeasure 1) := isProbabilityMeasure_expMeasure zero_lt_one
  have hcdf_lt : cdf (expMeasure 1) δ < 1 := by
    rw [cdf_expMeasure_eq zero_lt_one]
    split_ifs with hδ
    · have hexp : 0 < Real.exp (-((1 : ℝ) * δ)) := Real.exp_pos _
      linarith
    · norm_num
  have hIic_lt : expMeasure 1 (Iic δ) < 1 := by
    rw [← ofReal_cdf]
    simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hcdf_lt
  have hIio_lt : expMeasure 1 (Iio δ) < 1 :=
    (measure_mono Iio_subset_Iic_self).trans_lt hIic_lt
  intro hzero
  have hcomp : expMeasure 1 (Iio δ)ᶜ =
      expMeasure 1 Set.univ - expMeasure 1 (Iio δ) :=
    measure_compl measurableSet_Iio (measure_ne_top _ _)
  have hz : 1 - expMeasure 1 (Iio δ) = 0 := by
    calc
      1 - expMeasure 1 (Iio δ) =
          expMeasure 1 Set.univ - expMeasure 1 (Iio δ) := by rw [measure_univ]
      _ = expMeasure 1 (Iio δ)ᶜ := hcomp.symm
      _ = expMeasure 1 (Ici δ) := by rw [Set.compl_Iio]
      _ = 0 := hzero
  have hone : 1 ≤ expMeasure 1 (Iio δ) := tsub_eq_zero_iff_le.mp hz
  exact (not_lt_of_ge hone) hIio_lt

/-- Positive mass of the source mixture on its radial support. -/
theorem sourceRadialBase_Ici_ne_zero {η δ : ℝ}
    (hη1 : η < 1) :
    sourceRadialBase η (Ici δ) ≠ 0 := by
  have hweight : 0 < ENNReal.ofReal (1 - η) :=
    ENNReal.ofReal_pos.mpr (sub_pos.mpr hη1)
  have htail : 0 < expMeasure 1 (Ici δ) :=
    pos_iff_ne_zero.mpr (expMeasure_Ici_ne_zero δ)
  have hfirst : 0 < ENNReal.ofReal (1 - η) • expMeasure 1 (Ici δ) := by
    rw [smul_eq_mul]
    exact ENNReal.mul_pos hweight.ne' htail.ne'
  unfold sourceRadialBase
  rw [Measure.add_apply]
  exact ne_of_gt (add_pos_of_pos_of_nonneg hfirst bot_le)

/-- Exactly the radial law in equation (3.2): condition the source mixture
on `S ≥ δ`. -/
def sourceRadialLaw (η δ : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond (sourceRadialBase η) (Ici δ)

theorem isProbabilityMeasure_sourceRadialLaw {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    IsProbabilityMeasure (sourceRadialLaw η δ) := by
  let : IsProbabilityMeasure (sourceRadialBase η) :=
    isProbabilityMeasure_sourceRadialBase hη0 hη1.le
  apply ProbabilityTheory.cond_isProbabilityMeasure
  exact sourceRadialBase_Ici_ne_zero hη1

theorem sourceRadialLaw_apply_Ici {η δ : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η < 1) :
    sourceRadialLaw η δ (Ici δ) = 1 := by
  let : IsProbabilityMeasure (sourceRadialBase η) :=
    isProbabilityMeasure_sourceRadialBase hη0 hη1.le
  unfold sourceRadialLaw ProbabilityTheory.cond
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici,
    inter_self, smul_eq_mul, ENNReal.inv_mul_cancel]
  · exact sourceRadialBase_Ici_ne_zero hη1
  · exact measure_ne_top _ _

/-- Lebesgue-uniform law on a nondegenerate closed interval. -/
def sourceUniformInterval (a b : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc a b)

theorem isProbabilityMeasure_sourceUniformInterval {a b : ℝ} (hab : a < b) :
    IsProbabilityMeasure (sourceUniformInterval a b) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top.ne

theorem sourceUniformInterval_apply_self {a b : ℝ} (hab : a < b) :
    sourceUniformInterval a b (Icc a b) = 1 := by
  unfold sourceUniformInterval ProbabilityTheory.cond
  rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Icc,
    inter_self, smul_eq_mul, ENNReal.inv_mul_cancel]
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hab)
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top.ne

/-- The independent scalar coordinates `S`, `ξ`, and the two phases in
(3.18), encoded with right-associated products. -/
abbrev SourcePlantedScalars := ℝ × (ℝ × (ℝ × ℝ))

/-- Product law for the four scalar source coordinates: radial variable,
imbalance, and two independent phases. -/
def sourceScalarLaw (η δ ε : ℝ) : Measure SourcePlantedScalars :=
  (sourceRadialLaw η δ).prod
    ((sourceUniformInterval (-ε) ε).prod
      ((sourceUniformInterval 0 (2 * Real.pi)).prod
        (sourceUniformInterval 0 (2 * Real.pi))))

theorem isProbabilityMeasure_sourceScalarLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) :
    IsProbabilityMeasure (sourceScalarLaw η δ ε) := by
  let : IsProbabilityMeasure (sourceRadialLaw η δ) :=
    isProbabilityMeasure_sourceRadialLaw hη0 hη1
  let : IsProbabilityMeasure (sourceUniformInterval (-ε) ε) :=
    isProbabilityMeasure_sourceUniformInterval (by linarith)
  let : IsProbabilityMeasure (sourceUniformInterval 0 (2 * Real.pi)) :=
    isProbabilityMeasure_sourceUniformInterval (by positivity)
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- All independent coordinates of one planted source row. -/
abbrev SourcePlantedCoordinates (n : ℕ) := SourcePlantedScalars × Signal n

def sourceCoordinateLaw (η δ ε : ℝ) (n : ℕ) :
    Measure (SourcePlantedCoordinates n) :=
  (sourceScalarLaw η δ ε).prod (standardComplexGaussianTail n)

theorem isProbabilityMeasure_sourceCoordinateLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) (n : ℕ) :
    IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) := by
  let : IsProbabilityMeasure (sourceScalarLaw η δ ε) :=
    isProbabilityMeasure_sourceScalarLaw hη0 hη1 hε
  exact Measure.prod.instIsProbabilityMeasure _ _

/-- Equation (3.18), mapping independent source coordinates to a planted
column. -/
def sourcePlantedColumn {n : ℕ} (p : SourcePlantedCoordinates n) : Signal (n + 2) :=
  let S := p.1.1
  let ξ := p.1.2.1
  let α := p.1.2.2.1
  let β := p.1.2.2.2
  let w := p.2
  joinTwo
    ((Real.sqrt (S * (1 + ξ) / 2) : ℂ) * Complex.exp (α * Complex.I))
    ((Real.sqrt (S * (1 - ξ) / 2) : ℂ) * Complex.exp (β * Complex.I))
    w

theorem measurable_sourcePlantedColumn {n : ℕ} :
    Measurable (sourcePlantedColumn (n := n)) := by
  apply measurable_pi_lambda
  intro j
  by_cases hzero : j.1 = 0
  · simp [sourcePlantedColumn, joinTwo, hzero]
    fun_prop
  by_cases hone : j.1 = 1
  · simp [sourcePlantedColumn, joinTwo, hone]
    fun_prop
  · simp [sourcePlantedColumn, joinTwo, hzero, hone]
    fun_prop

/-- The source-specific planted column law in `ℂ^(n+2)`. -/
def sourcePlantedColumnLaw (η δ ε : ℝ) (n : ℕ) :
    Measure (Signal (n + 2)) :=
  (sourceCoordinateLaw η δ ε n).map sourcePlantedColumn

theorem isProbabilityMeasure_sourcePlantedColumnLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) (n : ℕ) :
    IsProbabilityMeasure (sourcePlantedColumnLaw η δ ε n) := by
  let : IsProbabilityMeasure (sourceCoordinateLaw η δ ε n) :=
    isProbabilityMeasure_sourceCoordinateLaw hη0 hη1 hε n
  exact Measure.isProbabilityMeasure_map measurable_sourcePlantedColumn.aemeasurable

/-- IID planted columns, one for every row of a source frame. -/
def iidSourcePlantedColumnLaw (η δ ε : ℝ) (m n : ℕ) :
    Measure (Fin m → Signal (n + 2)) :=
  Measure.pi (fun _ ↦ sourcePlantedColumnLaw η δ ε n)

theorem isProbabilityMeasure_iidSourcePlantedColumnLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) (m n : ℕ) :
    IsProbabilityMeasure (iidSourcePlantedColumnLaw η δ ε m n) := by
  exact @MeasureTheory.Measure.pi.instIsProbabilityMeasure
    (Fin m) (fun _ ↦ Signal (n + 2)) _ _
    (fun _ ↦ sourcePlantedColumnLaw η δ ε n)
    (fun _ ↦ isProbabilityMeasure_sourcePlantedColumnLaw hη0 hη1 hε n)

/-- Translate planted columns into the row convention used by the frame
predicate and by the manuscript. -/
def frameFromPlantedColumns {m n : ℕ} (a : Fin m → Signal (n + 2)) :
    Frame m (n + 2) := fun i ↦ star (a i)

theorem measurable_frameFromPlantedColumns {m n : ℕ} :
    Measurable (frameFromPlantedColumns (m := m) (n := n)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun a : Fin m → Signal (n + 2) ↦ star (a i j))
  fun_prop

/-- The iid planted-frame law, in fixed planted coordinates. -/
def iidSourcePlantedFrameLaw (η δ ε : ℝ) (m n : ℕ) :
    Measure (Frame m (n + 2)) :=
  (iidSourcePlantedColumnLaw η δ ε m n).map frameFromPlantedColumns

theorem isProbabilityMeasure_iidSourcePlantedFrameLaw
    {η δ ε : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε) (m n : ℕ) :
    IsProbabilityMeasure (iidSourcePlantedFrameLaw η δ ε m n) := by
  let : IsProbabilityMeasure (iidSourcePlantedColumnLaw η δ ε m n) :=
    isProbabilityMeasure_iidSourcePlantedColumnLaw hη0 hη1 hε m n
  exact Measure.isProbabilityMeasure_map measurable_frameFromPlantedColumns.aemeasurable

/-- The numerical planted law used in Proposition 3.1, before Haar averaging,
at the source row and tail dimensions. -/
def sourcePlantedFrameLawAt (M : ℕ) :
    Measure (Frame (sourceRowCount M) (sourceTailDimension M + 2)) :=
  iidSourcePlantedFrameLaw sourceEta (sourceDelta M) (sourceEpsilon M)
    (sourceRowCount M) (sourceTailDimension M)

theorem isProbabilityMeasure_sourcePlantedFrameLawAt
    {M : ℕ} (hM : 1 ≤ M) :
    IsProbabilityMeasure (sourcePlantedFrameLawAt M) := by
  apply isProbabilityMeasure_iidSourcePlantedFrameLaw sourceEta_pos.le sourceEta_lt_one
  exact sourceEpsilon_pos M hM

theorem sourceTailDimension_add_two {M : ℕ} (hM : 2 ≤ M) :
    sourceTailDimension M + 2 = M := by
  unfold sourceTailDimension
  lia

end NLA.FR05

end
end

/-! ## SourceConditional -/

section

/-
Conditional-product assembly for one source planted row.

The scalar coordinates and complex-Gaussian tail are independent in the
actual source law.  This makes the preceding product-section lemma directly
available for the tail conditional estimates in Lemma 3.6.
-/


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace NLA.FR05

/-- A uniform conditional bound over the independent Gaussian tail holds for
the complete source-coordinate law of one planted row. -/
theorem sourceCoordinateLaw_le_of_tail_sections_le
    {η δ ε : ℝ} (n : ℕ) (hη0 : 0 ≤ η) (hη1 : η < 1) (hε : 0 < ε)
    {s : Set (SourcePlantedCoordinates n)} (hs : MeasurableSet s) (c : ℝ≥0∞)
    (hsection : ∀ q : SourcePlantedScalars,
      standardComplexGaussianTail n {w | (q, w) ∈ s} ≤ c) :
    sourceCoordinateLaw η δ ε n s ≤ c := by
  let : IsProbabilityMeasure (sourceScalarLaw η δ ε) :=
    isProbabilityMeasure_sourceScalarLaw hη0 hη1 hε
  unfold sourceCoordinateLaw
  exact prod_measure_le_of_sections_le (sourceScalarLaw η δ ε)
    (standardComplexGaussianTail n) hs c hsection

end NLA.FR05

end

end
