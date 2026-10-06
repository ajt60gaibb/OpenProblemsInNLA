import Mathlib
import LeanCert.Tactic.Verification

/-! Unconditional geometry of reflected translated intersections, preparatory
to the Gaussian shift theorem. No Brunn–Minkowski inequality is assumed. -/

set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory
noncomputable section
namespace NLA.IE06.GaussianShiftGeometry

def translatedIntersection {E : Type*} [Sub E] (K C : Set E) (v : E) : Set E :=
  {x | x ∈ K ∧ x - v ∈ C}

def CentrallySymmetric {E : Type*} [Neg E] (K : Set E) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

theorem reflected_mem {E : Type*} [AddCommGroup E] {K C : Set E}
    (hK : CentrallySymmetric K) (hC : CentrallySymmetric C) (v x : E) :
    x ∈ translatedIntersection K C v ↔
      -x ∈ translatedIntersection K C (-v) := by
  change (x ∈ K ∧ x - v ∈ C) ↔ (-x ∈ K ∧ -x - -v ∈ C)
  rw [hK x, hC (x-v)]
  simp only [sub_eq_add_neg, neg_add_rev, neg_neg, add_comm]

theorem neg_preimage_intersection {E : Type*} [AddCommGroup E] {K C : Set E}
    (hK : CentrallySymmetric K) (hC : CentrallySymmetric C) (v : E) :
    (fun x : E => -x) ⁻¹' translatedIntersection K C (-v) =
      translatedIntersection K C v := by
  ext x
  exact (reflected_mem hK hC v x).symm

theorem midpoint_mem_intersection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K C : Set E} (hK : Convex ℝ K) (hC : Convex ℝ C) {v x y : E}
    (hx : x ∈ translatedIntersection K C v)
    (hy : y ∈ translatedIntersection K C (-v)) :
    midpoint ℝ x y ∈ K ∩ C := by
  constructor
  · exact hK.midpoint_mem hx.1 hy.1
  · have hm := hC.midpoint_mem hx.2 hy.2
    have he : midpoint ℝ (x-v) (y-(-v)) = midpoint ℝ x y := by
      simp only [midpoint_eq_smul_add, sub_neg_eq_add]
      congr 1
      abel
    rwa [he] at hm

theorem midpoints_subset_intersection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K C : Set E} (hK : Convex ℝ K) (hC : Convex ℝ C) (v : E) :
    {z | ∃ x ∈ translatedIntersection K C v,
      ∃ y ∈ translatedIntersection K C (-v), z = midpoint ℝ x y} ⊆ K ∩ C := by
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact midpoint_mem_intersection hK hC hx hy

theorem translatedIntersection_measurable {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {K C : Set E}
    (hK : MeasurableSet K) (hC : MeasurableSet C) (v : E) :
    MeasurableSet (translatedIntersection K C v) :=
  hK.inter (hC.preimage (measurable_id.sub_const v))

theorem translatedIntersection_volume_reflection {a : ℕ}
    {K C : Set (EuclideanSpace ℝ (Fin a))}
    (hK : CentrallySymmetric K) (hC : CentrallySymmetric C)
    (hmK : MeasurableSet K) (hmC : MeasurableSet C)
    (v : EuclideanSpace ℝ (Fin a)) :
    volume (translatedIntersection K C v) = volume (translatedIntersection K C (-v)) := by
  rw [← neg_preimage_intersection hK hC v]
  exact (Measure.measurePreserving_neg volume).measure_preimage
    (translatedIntersection_measurable hmK hmC (-v)).nullMeasurableSet

#assert_trust kernel translatedIntersection
#assert_trust kernel CentrallySymmetric
#assert_trust kernel reflected_mem
#assert_trust kernel neg_preimage_intersection
#assert_trust kernel midpoint_mem_intersection
#assert_trust kernel midpoints_subset_intersection
#assert_trust kernel translatedIntersection_measurable
#assert_trust kernel translatedIntersection_volume_reflection

#print axioms translatedIntersection
#print axioms CentrallySymmetric
#print axioms reflected_mem
#print axioms neg_preimage_intersection
#print axioms midpoint_mem_intersection
#print axioms midpoints_subset_intersection
#print axioms translatedIntersection_measurable
#print axioms translatedIntersection_volume_reflection

end NLA.IE06.GaussianShiftGeometry
