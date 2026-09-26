/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.

Supporting bounded-volume statements A/B were independently reviewed before
implementation; evidence/finite-volume-preproof-review.json records that review.
These hypotheses are not hypotheses of the frozen TR-06 final theorems.
-/
import NLA.TR06.Rectangular

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal
open MeasureTheory Set Function

namespace NLA.TR06.Area

section Overlap
variable {E : Type*} [MeasurableSpace E]
  (μ : Measure E) {V : Set E} {t : ℕ → Set E} {B : ℕ}

/-- Finite overlap controls the sum of the measures, even for a nonmeasurable
containing set V. Measurability is needed only for the individual pieces. -/
theorem sum_measure_le_of_bounded_overlap
    (ht : ∀ j, MeasurableSet (t j)) (hV : ∀ j, t j ⊆ V)
    (hB : ∀ x, (∑' j, (t j).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ B) :
    (∑' j, μ (t j)) ≤ (B : ℝ≥0∞) * μ V := by
  classical
  calc
    (∑' j, μ (t j)) = ∫⁻ x, ∑' j, (t j).indicator (fun _ => (1 : ℝ≥0∞)) x ∂μ := by
      rw [lintegral_tsum (fun j => (measurable_const.indicator (ht j)).aemeasurable)]
      simp only [lintegral_indicator_const (ht _), one_mul]
    _ ≤ ∫⁻ x, V.indicator (fun _ => (B : ℝ≥0∞)) x ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ V
      · simpa only [indicator_of_mem hx] using hB x
      · have hxj : ∀ j, x ∉ t j := fun j h => hx (hV j h)
        simp only [indicator_of_notMem hx, indicator_of_notMem (hxj _), tsum_zero, le_refl]
    _ ≤ (B : ℝ≥0∞) * μ V := lintegral_indicator_const_le V B

end Overlap

section Volume
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {V : Set E} {t : ℕ → Set E} {f : ℕ → E → F} {K : ℝ≥0} {B : ℕ}

/-- Statement A: a countable uniformly Lipschitz cover with uniformly bounded
base overlap has finite Euclidean Hausdorff volume, with an explicit bound.
No image-measurability hypothesis is used. -/
theorem finite_volume_of_bounded_overlap
    (hVfinite : volume V < ⊤)
    (ht : ∀ j, MeasurableSet (t j)) (hV : ∀ j, t j ⊆ V)
    (hf : ∀ j, LipschitzOnWith K (f j) (t j))
    (hB : ∀ x, (∑' j, (t j).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ B) :
    (μHE[Module.finrank ℝ E] : Measure F) (⋃ j, f j '' t j) ≤
        (K : ℝ≥0∞) ^ Module.finrank ℝ E * (B : ℝ≥0∞) * volume V ∧
    (μHE[Module.finrank ℝ E] : Measure F) (⋃ j, f j '' t j) < ⊤ := by
  have hbound : (μHE[Module.finrank ℝ E] : Measure F) (⋃ j, f j '' t j) ≤
      (K : ℝ≥0∞) ^ Module.finrank ℝ E * (B : ℝ≥0∞) * volume V := by
    calc
      _ ≤ ∑' j, (μHE[Module.finrank ℝ E] : Measure F) (f j '' t j) := measure_iUnion_le _
      _ ≤ ∑' j, (K : ℝ≥0∞) ^ Module.finrank ℝ E * volume (t j) := by
        apply ENNReal.tsum_le_tsum
        intro j
        simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
          euclidean_image_le_of_lipschitzOn (hf j) (Module.finrank ℝ E)
      _ = (K : ℝ≥0∞) ^ Module.finrank ℝ E * ∑' j, volume (t j) :=
        ENNReal.tsum_mul_left
      _ ≤ (K : ℝ≥0∞) ^ Module.finrank ℝ E * ((B : ℝ≥0∞) * volume V) :=
by
        gcongr
        exact sum_measure_le_of_bounded_overlap volume ht hV hB
      _ = _ := (mul_assoc _ _ _).symm
  refine ⟨hbound, hbound.trans_lt ?_⟩
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
    (ENNReal.natCast_lt_top B)) hVfinite

end Volume

section Fibers
variable {E F : Type*} {π : F → E} {S : Set F}
  {t : ℕ → Set E} {f : ℕ → E → F} {B : ℕ}

/-- Statement B: disjoint inverse branches transfer a uniform finite-subset
fiber bound to the base-overlap bound needed in Statement A. -/
theorem bounded_overlap_of_fiber_bound
    (hπ : ∀ j, ∀ x ∈ t j, π (f j x) = x)
    (hdisj : Pairwise (Disjoint on fun j => f j '' t j))
    (hS : ∀ j, f j '' t j ⊆ S)
    (hB : ∀ x (q : Finset F), (↑q : Set F) ⊆ {z | z ∈ S ∧ π z = x} → q.card ≤ B) :
    ∀ x, (∑' j, (t j).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤ B := by
  classical
  intro x
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun q => ?_
  let a := q.filter (fun j => x ∈ t j)
  have hainj : Set.InjOn (fun j => f j x) (↑a : Set ℕ) := by
    intro i hi j hj heq
    by_contra hij
    exact Set.disjoint_left.mp (hdisj hij) ⟨x, (Finset.mem_filter.mp hi).2, rfl⟩
      ⟨x, (Finset.mem_filter.mp hj).2, heq.symm⟩
  have haB : a.card ≤ B := by
    rw [← Finset.card_image_of_injOn hainj]
    apply hB x (a.image (fun j => f j x))
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact ⟨hS j ⟨x, (Finset.mem_filter.mp hj).2, rfl⟩,
      hπ j x (Finset.mem_filter.mp hj).2⟩
  calc
    (∑ j ∈ q, (t j).indicator (fun _ => (1 : ℝ≥0∞)) x) = (a.card : ℝ≥0∞) := by
      simp only [a, indicator_apply, Finset.sum_boole]
    _ ≤ (B : ℝ≥0∞) := by exact_mod_cast haB

end Fibers

#print axioms sum_measure_le_of_bounded_overlap
#print axioms finite_volume_of_bounded_overlap
#print axioms bounded_overlap_of_fiber_bound
#assert_trust kernel sum_measure_le_of_bounded_overlap
#assert_trust kernel finite_volume_of_bounded_overlap
#assert_trust kernel bounded_overlap_of_fiber_bound

end NLA.TR06.Area
