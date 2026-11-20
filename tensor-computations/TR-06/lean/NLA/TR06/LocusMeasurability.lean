/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Measurability
import NLA.TR06.RankOneCharts

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Set MeasureTheory
namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem regularSet_subset_identifiable :
    regularSet d n r ⊆ identifiableRealSet d n r := by
  rintro A ⟨c, u, hu, rfl⟩
  exact (c.chart u).property

theorem smoothRegularSet_subset_sourceSmoothSet :
    smoothRegularSet d n r ⊆ sourceSmoothSet d n r := by
  rintro A ⟨c, u, hu, hA⟩
  exact ⟨c.toSourceSmoothChart, u, hu, hA⟩

theorem smoothRegularSet_subset_identifiable :
    smoothRegularSet d n r ⊆ identifiableRealSet d n r :=
  smoothRegularSet_subset_sourceSmoothSet.trans sourceSmoothSet_subset_identifiable

/-- Actual open chart targets show relative openness; no assertion that an
uncountable union of Borel sets is Borel is used. -/
theorem regularSet_relatively_open :
    IsOpen {A : identifiableRealSet d n r | A.val ∈ regularSet d n r} := by
  rw [isOpen_iff_mem_nhds]
  rintro A ⟨c, u, hu, heq⟩
  have heq' : c.chart u = A := Subtype.ext heq
  have htarget : A ∈ c.chart.target := heq' ▸ c.chart.map_source hu
  filter_upwards [c.chart.open_target.mem_nhds htarget] with B hB
  exact ⟨c, c.chart.symm B, c.chart.map_target hB,
    congrArg Subtype.val (c.chart.right_inv hB)⟩

theorem smoothRegularSet_relatively_open :
    IsOpen {A : identifiableRealSet d n r | A.val ∈ smoothRegularSet d n r} := by
  rw [isOpen_iff_mem_nhds]
  rintro A ⟨c, u, hu, heq⟩
  have heq' : c.chart u = A := Subtype.ext heq
  have htarget : A ∈ c.chart.target := heq' ▸ c.chart.map_source hu
  filter_upwards [c.chart.open_target.mem_nhds htarget] with B hB
  exact ⟨c, c.chart.symm B, c.chart.map_target hB,
    congrArg Subtype.val (c.chart.right_inv hB)⟩

private theorem measurableSet_of_relative_open {s t : Set (Tensor ℝ d n)}
    (hs : MeasurableSet s) (hts : t ⊆ s)
    (ht : IsOpen {A : s | A.val ∈ t}) : MeasurableSet t := by
  have hmeas := hs.subtype_image ht.measurableSet
  have heq : Subtype.val '' {A : s | A.val ∈ t} = t := by
    ext A
    constructor
    · rintro ⟨B, hB, rfl⟩
      exact hB
    · intro hA
      exact ⟨⟨A, hts hA⟩, hA, rfl⟩
  rwa [heq] at hmeas

/-- Borel measurability of the full C1 decomposition-chart locus. -/
theorem measurableSet_regularSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet (regularSet d n r) :=
  measurableSet_of_relative_open (measurableSet_identifiableRealSet d n r)
    regularSet_subset_identifiable regularSet_relatively_open

/-- Borel measurability of the source's smooth identifiable input locus. -/
theorem measurableSet_sourceSmoothSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet (sourceSmoothSet d n r) :=
  measurableSet_of_relative_open (measurableSet_identifiableRealSet d n r)
    sourceSmoothSet_subset_identifiable sourceSmoothSet_relatively_open

/-- Borel measurability of the locus with smooth decomposition charts. No
existence, full-measure, or volume correspondence conclusion is asserted. -/
theorem measurableSet_smoothRegularSet (d : ℕ) (n : Fin d → ℕ) (r : ℕ) :
    MeasurableSet (smoothRegularSet d n r) :=
  measurableSet_of_relative_open (measurableSet_identifiableRealSet d n r)
    smoothRegularSet_subset_identifiable smoothRegularSet_relatively_open

#print axioms regularSet_subset_identifiable
#print axioms smoothRegularSet_subset_sourceSmoothSet
#print axioms smoothRegularSet_subset_identifiable
#print axioms regularSet_relatively_open
#print axioms smoothRegularSet_relatively_open
#print axioms measurableSet_regularSet
#print axioms measurableSet_sourceSmoothSet
#print axioms measurableSet_smoothRegularSet
#assert_trust kernel regularSet_subset_identifiable
#assert_trust kernel smoothRegularSet_subset_sourceSmoothSet
#assert_trust kernel smoothRegularSet_subset_identifiable
#assert_trust kernel regularSet_relatively_open
#assert_trust kernel smoothRegularSet_relatively_open
#assert_trust kernel measurableSet_regularSet
#assert_trust kernel measurableSet_sourceSmoothSet
#assert_trust kernel measurableSet_smoothRegularSet
end NLA.TR06
