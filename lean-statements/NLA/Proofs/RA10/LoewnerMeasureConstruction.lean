import NLA.Proofs.RA10.CompactLoewnerEndpoint
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Analysis.Convex.Hull

/-! Construct a positive representing measure from approximation by harmonic atoms.
The construction uses compactness of probability measures on [0,1]. It does not
assume a representing measure exists. Connecting arbitrary admissible functions
to the closed convex hull of the atoms is proved separately in
`OperatorMonotoneRepresentation`. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory NLA.Statements.RA10 Set

namespace NLA.Proofs.RA10

abbrev PositiveArgument := Set.Ioi (0 : ℝ)

noncomputable def loewnerProfile (t : LoewnerParameter) : PositiveArgument → ℝ :=
  fun x => loewnerAtom t x

noncomputable def probabilityLoewnerProfile (μ : ProbabilityMeasure LoewnerParameter) :
    PositiveArgument → ℝ := fun x => ∫ t, loewnerAtom t x ∂μ

theorem loewnerAtom_denominator_pos (t : LoewnerParameter) {x : ℝ} (hx : 0 < x) :
    0 < (t : ℝ) + (1 - (t : ℝ)) * x := by
  by_cases ht : (t : ℝ) = 0
  · simpa [ht] using hx
  · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne t.property.1 (Ne.symm ht))
      (mul_nonneg (sub_nonneg.mpr t.property.2) hx.le)

theorem loewnerAtom_eq_fraction (t : LoewnerParameter) {x : ℝ} (hx : 0 < x) :
    loewnerAtom t x = x / ((t : ℝ) + (1 - (t : ℝ)) * x) := by
  by_cases ht : (t : ℝ) = 0 <;> simp [loewnerAtom, ht, hx.ne']

/-- At positive arguments the parameter kernel is continuous even at both endpoints. -/
theorem loewnerAtom_continuous_parameter {x : ℝ} (hx : 0 < x) :
    Continuous (fun t : LoewnerParameter => loewnerAtom t x) := by
  simp_rw [loewnerAtom_eq_fraction _ hx]
  exact continuous_const.div
    (continuous_subtype_val.add ((continuous_const.sub continuous_subtype_val).mul
      continuous_const)) (fun t => (loewnerAtom_denominator_pos t hx).ne')

theorem probabilityLoewnerProfile_continuous : Continuous probabilityLoewnerProfile := by
  apply continuous_pi
  intro x
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (show C(LoewnerParameter, ℝ) from
      ⟨fun t => loewnerAtom t x, loewnerAtom_continuous_parameter x.property⟩)

theorem probabilityLoewnerProfile_range_isCompact :
    IsCompact (Set.range probabilityLoewnerProfile) :=
  isCompact_range probabilityLoewnerProfile_continuous

theorem probabilityLoewnerProfile_range_isClosed :
    IsClosed (Set.range probabilityLoewnerProfile) :=
  probabilityLoewnerProfile_range_isCompact.isClosed

theorem probabilityLoewnerProfile_range_convex :
    Convex ℝ (Set.range probabilityLoewnerProfile) := by
  intro f hf g hg a b ha hb hab
  obtain ⟨μ, rfl⟩ := hf
  obtain ⟨ν, rfl⟩ := hg
  let ρ : Measure LoewnerParameter :=
    ENNReal.ofReal a • (μ : Measure LoewnerParameter) +
      ENNReal.ofReal b • (ν : Measure LoewnerParameter)
  have hρ : IsProbabilityMeasure ρ := by
    constructor
    simp only [ρ, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab]
    norm_num
  refine ⟨⟨ρ, hρ⟩, ?_⟩
  funext x
  change (∫ t, loewnerAtom t x ∂ρ) = a * (∫ t, loewnerAtom t x ∂μ) +
    b * (∫ t, loewnerAtom t x ∂ν)
  rw [integral_add_measure
    ((loewnerAtom_integrable (μ : Measure LoewnerParameter) x.property.le).smul_measure
      ENNReal.ofReal_ne_top)
    ((loewnerAtom_integrable (ν : Measure LoewnerParameter) x.property.le).smul_measure
      ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb,
    smul_eq_mul]

theorem loewnerProfile_mem_probability_range (t : LoewnerParameter) :
    loewnerProfile t ∈ Set.range probabilityLoewnerProfile := by
  refine ⟨⟨Measure.dirac t, inferInstance⟩, ?_⟩
  funext x
  simp [probabilityLoewnerProfile, loewnerProfile]

/-- Every pointwise limit of convex combinations of atoms has a representing
probability measure. Compactness supplies the measure; no sequence or subnet
needs to be chosen explicitly. -/
theorem exists_probabilityMeasure_of_mem_closedConvexHull {f : PositiveArgument → ℝ}
    (hf : f ∈ closure (convexHull ℝ (Set.range loewnerProfile))) :
    ∃ μ : ProbabilityMeasure LoewnerParameter, ∀ x : PositiveArgument,
      f x = ∫ t, loewnerAtom t x ∂μ := by
  have hsubset : closure (convexHull ℝ (Set.range loewnerProfile)) ⊆
      Set.range probabilityLoewnerProfile :=
    closure_minimal
      (convexHull_min (by rintro _ ⟨t, rfl⟩; exact loewnerProfile_mem_probability_range t)
        probabilityLoewnerProfile_range_convex)
      probabilityLoewnerProfile_range_isClosed
  obtain ⟨μ, hμ⟩ := hsubset hf
  exact ⟨μ, fun x => (congrFun hμ x).symm⟩

/-- For a function continuous at the boundary, the constructed measure also
represents the value at zero. -/
theorem hasCompactLoewnerRepresentation_of_mem_closedConvexHull {f : ℝ → ℝ}
    (hc : ContinuousOn f (Set.Ici 0))
    (hf : (fun x : PositiveArgument => f x) ∈ closure (convexHull ℝ (Set.range loewnerProfile))) :
    HasCompactLoewnerRepresentation f := by
  obtain ⟨μ, hμ⟩ := exists_probabilityMeasure_of_mem_closedConvexHull hf
  refine ⟨(μ : Measure LoewnerParameter), inferInstance, ?_⟩
  exact compactLoewnerRepresentation_extend_zero hc _ fun x hx => hμ ⟨x, hx⟩

/-- In particular, pointwise convergent sequences or nets of finite convex
combinations produce a single probability measure representing every argument. -/
theorem exists_probabilityMeasure_of_tendsto_convexCombinations
    {ι : Type*} {l : Filter ι} [l.NeBot] {g : ι → PositiveArgument → ℝ}
    {f : PositiveArgument → ℝ}
    (hg : ∀ i, g i ∈ convexHull ℝ (Set.range loewnerProfile))
    (hlim : ∀ x, Filter.Tendsto (fun i => g i x) l (nhds (f x))) :
    ∃ μ : ProbabilityMeasure LoewnerParameter, ∀ x : PositiveArgument,
      f x = ∫ t, loewnerAtom t x ∂μ := by
  apply exists_probabilityMeasure_of_mem_closedConvexHull
  exact isClosed_closure.mem_of_tendsto (tendsto_pi_nhds.mpr hlim)
    (Filter.Eventually.of_forall fun i => subset_closure (hg i))

#assert_trust kernel loewnerAtom_denominator_pos
#assert_trust kernel loewnerAtom_eq_fraction
#assert_trust kernel loewnerAtom_continuous_parameter
#assert_trust kernel probabilityLoewnerProfile_continuous
#assert_trust kernel probabilityLoewnerProfile_range_isCompact
#assert_trust kernel probabilityLoewnerProfile_range_isClosed
#assert_trust kernel probabilityLoewnerProfile_range_convex
#assert_trust kernel loewnerProfile_mem_probability_range
#assert_trust kernel exists_probabilityMeasure_of_mem_closedConvexHull
#assert_trust kernel hasCompactLoewnerRepresentation_of_mem_closedConvexHull
#assert_trust kernel exists_probabilityMeasure_of_tendsto_convexCombinations
#print axioms exists_probabilityMeasure_of_mem_closedConvexHull

end NLA.Proofs.RA10
