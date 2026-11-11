/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original TR-06 mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.PivotChart

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators Topology
open Set Filter
namespace NLA.TR06.Proposed
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

theorem contDiffOn_normalizedTuple
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a : E → Fin r → Tensor ℝ d n} {S : Set E} {k : WithTop ℕ∞}
    (ha : ∀ i, ContDiffOn ℝ k (fun x => a x i) S)
    (hnz : ∀ x ∈ S, ∀ i, a x i ≠ 0) :
    ContDiffOn ℝ k (fun x => normalizedTuple (a x)) S := by
  apply (contDiffOn_piLp 2).mpr
  intro iq
  change ContDiffOn ℝ k (fun x => a x iq.1 iq.2 / ‖a x iq.1‖) S
  exact ((contDiff_piLp_apply 2 (i := iq.2)).comp_contDiffOn (ha iq.1)).div
    ((ha iq.1).norm ℝ (fun x hx => hnz x hx iq.1))
    (fun x hx => norm_ne_zero_iff.mpr (hnz x hx iq.1))

/-- Proper addition and an actual Segre immersion construct the entire frozen
smooth chart, with its full identifiable-locus topology and ordered branch. -/
theorem smooth_chart_of_proper_immersion : SmoothChartOfProperImmersionStatement := by
  classical
  intro d n r hd U hU hgood hproper q₀ z hznz hzU hzinj
  let j₀ : Fin d := ⟨0, hd⟩
  let V : Set (OrderedPivotData q₀) :=
    {p | ∀ i, (p i).1 ≠ 0} ∩ (pivotSum q₀) ⁻¹' U
  have hV : IsOpen V := (isOpen_orderedNonzeroPivotData q₀).inter
    (hU.preimage (contDiff_pivotSum q₀ 1).continuous)
  obtain ⟨W, hW, hzW, hWV, hWinj, hWderiv⟩ :=
    exists_immersion_patch (contDiff_pivotSum q₀ 1) hzinj hV ⟨hznz, hzU⟩
  have hWnz : ∀ p ∈ W, ∀ i, (p i).1 ≠ 0 := fun p hp => (hWV hp).1
  have hWU : ∀ p ∈ W, pivotSum q₀ p ∈ U := fun p hp => (hWV hp).2
  obtain ⟨e, heW, heval⟩ := exists_pivot_open_chart U hU hgood hproper q₀ j₀ W hW
    ⟨z, hzW⟩ hWnz hWU hWinj
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin (expectedDimension d n r))) =
      Module.finrank ℝ (OrderedPivotData q₀) := by
    rw [finrank_euclideanSpace_fin, finrank_orderedPivotData]
  let ξ : EuclideanSpace ℝ (Fin (expectedDimension d n r)) ≃L[ℝ] OrderedPivotData q₀ :=
    ContinuousLinearEquiv.ofFinrankEq hdim
  let chart := ξ.toHomeomorph.toOpenPartialHomeomorph.trans e
  have hsource (u) : u ∈ chart.source ↔ ξ u ∈ W := by
    change (u ∈ Set.univ ∧ ξ u ∈ e.source) ↔ ξ u ∈ W
    rw [heW]
    simp
  have hinput (u) (hu : u ∈ chart.source) : (chart u).val = pivotSum q₀ (ξ u) :=
    heval (ξ u) ((hsource u).mp hu)
  let summands := fun u => orderedTensorFromPivotData q₀ (ξ u)
  have hdecomp (u) (hu : u ∈ chart.source) : Decomposes (summands u) (chart u).val := by
    refine ⟨fun i => tensorFromPivotData_rankOne (q₀ i) j₀ (ξ u i)
      (hWnz (ξ u) ((hsource u).mp hu) i), ?_⟩
    exact (hinput u hu).symm
  have hsumsm : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => summands u i) := by
    intro i
    exact contDiff_pi.mp ((contDiff_orderedTensorFromPivotData q₀ _).comp ξ.contDiff) i
  have hinputsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => (chart u).val) chart.source := by
    exact ((contDiff_pivotSum q₀ _).comp ξ.contDiff).contDiffOn.congr hinput
  have hinputinj : ∀ u ∈ chart.source,
      Function.Injective (fderiv ℝ (fun v => (chart v).val) u) := by
    intro u hu
    have hevent : (fun v => (chart v).val) =ᶠ[𝓝 u] (fun v => pivotSum q₀ (ξ v)) := by
      filter_upwards [chart.open_source.mem_nhds hu] with v hv using hinput v hv
    have hderiv := ((contDiff_pivotSum q₀ 1).differentiable one_ne_zero).differentiableAt (x := ξ u) |>.hasFDerivAt
    have hcderiv := (hderiv.comp u ξ.hasFDerivAt).congr_of_eventuallyEq hevent
    rw [hcderiv.fderiv]
    exact (hWderiv (ξ u) ((hsource u).mp hu)).comp ξ.injective
  let c : SmoothDecompositionChart d n r :=
    { chart := chart
      input_smooth := hinputsm
      input_injective_derivative := hinputinj
      summands := summands
      decomposes := hdecomp
      summands_smooth := fun i => (hsumsm i).contDiffOn
      output_smooth := contDiffOn_normalizedTuple (fun i => (hsumsm i).contDiffOn)
        (fun u hu i => (hdecomp u hu).1 i |>.1) }
  have hbase : ξ.symm z ∈ c.chart.source := by
    exact (hsource _).mpr (by simpa using hzW)
  refine ⟨c, ξ.symm z, hbase, ?_, ?_, ?_⟩
  · exact (hinput _ hbase).trans (by rw [ξ.apply_symm_apply])
  · change orderedTensorFromPivotData q₀ (ξ (ξ.symm z)) = _
    rw [ξ.apply_symm_apply]
  · intro v hv
    rw [show (c.chart v).val = pivotSum q₀ (ξ v) from hinput v hv]
    exact hWU (ξ v) ((hsource v).mp hv)

/-- Every actual identifiable tensor on a certified proper immersion open
belongs to the frozen smooth regular locus. -/
theorem smooth_regular_on_proper_immersion : SmoothRegularOnProperImmersionStatement := by
  classical
  intro d n r hd U hU hgood hproper himm A hA
  obtain ⟨a, ha⟩ := hA.2.1.1
  have hpiv (i : Fin r) : ∃ q : TensorIndex d n, a i q ≠ 0 := by
    by_contra h
    push Not at h
    apply (ha.1 i).1
    ext q
    exact h q
  choose q₀ hq₀ using hpiv
  let z := orderedTensorToPivotData q₀ a
  have hznz : ∀ i, (z i).1 ≠ 0 := hq₀
  have hdecode : orderedTensorFromPivotData q₀ z = a := by
    funext i
    exact tensorFromPivotData_to (q₀ i) (a i) (ha.1 i) (hq₀ i)
  have hsum : pivotSum q₀ z = A := by
    change (∑ i, orderedTensorFromPivotData q₀ z i) = A
    rw [hdecode]
    exact ha.2
  have hzU : pivotSum q₀ z ∈ U := hsum.symm ▸ hA.1
  obtain ⟨c, u, hu, hcu, _horder, _hU⟩ := smooth_chart_of_proper_immersion d n r hd U hU
    hgood hproper q₀ z hznz hzU (himm q₀ z hznz hzU)
  exact ⟨c, u, hu, hcu.trans hsum⟩

#print axioms contDiffOn_normalizedTuple
#print axioms smooth_chart_of_proper_immersion
#assert_trust kernel contDiffOn_normalizedTuple
#assert_trust kernel smooth_chart_of_proper_immersion
#print axioms smooth_regular_on_proper_immersion
#assert_trust kernel smooth_regular_on_proper_immersion
end NLA.TR06.Proposed
