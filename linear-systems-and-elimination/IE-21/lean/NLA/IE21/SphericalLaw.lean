import NLA.IE21.Definitions

/-!
The actual normalized Euclidean surface measure used in IE-21.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

namespace NLA.IE21

theorem surface_probability (n : ℕ) (hn : 1 ≤ n) :
    0 < surfaceMeasure n Set.univ ∧ surfaceMeasure n Set.univ < ⊤ ∧
    IsProbabilityMeasure (surfaceLaw n) ∧ IsProbabilityMeasure (sphereLaw n) ∧
    (sphereLaw n) {u | ‖u‖ = 1} = 1 := by
  let : NeZero n := ⟨by omega⟩
  have hs : surfaceMeasure n ≠ 0 := Measure.toSphere_ne_zero volume
  let : NeZero (surfaceMeasure n) := ⟨hs⟩
  let : IsFiniteMeasure (surfaceMeasure n) := inferInstanceAs
    (IsFiniteMeasure (volume : Measure (Space n)).toSphere)
  have hp : IsProbabilityMeasure (surfaceLaw n) := by
    unfold surfaceLaw
    infer_instance
  let := hp
  have hq : IsProbabilityMeasure (sphereLaw n) :=
    Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
  refine ⟨pos_iff_ne_zero.mpr (by simpa using hs), measure_lt_top _ _, hp, hq, ?_⟩
  rw [sphereLaw, Measure.map_apply measurable_subtype_coe
    (isClosed_eq continuous_norm continuous_const).measurableSet]
  have hpre : Subtype.val ⁻¹' {u : Space n | ‖u‖ = 1} = (univ : Set (Sphere n)) := by
    ext u
    simp only [mem_preimage, mem_ofPred_eq, mem_univ, iff_true]
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  rw [hpre, measure_univ]

theorem measurable_gaussianDirection (n : ℕ) : Measurable (@gaussianDirection n) := by
  unfold gaussianDirection
  fun_prop

theorem gaussian_projection_law {n : ℕ} (x : Space n) (hx : ‖x‖ = 1) :
    (stdGaussian (Space n)).map (fun g => inner ℝ x g) = gaussianReal 0 1 := by
  change (stdGaussian (Space n)).map (innerSL ℝ x) = _
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]
  simp [hx]

end NLA.IE21
