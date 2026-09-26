/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, George Stepaniants
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology.

The partition-and-integration assembly adapts Mathlib's
MeasureTheory/Function/Jacobian.lean (Sébastien Gouëzel). Its new local
rectangular estimates use Hausdorff distortion, not ambient thickenings.
-/
import NLA.TR06.Radius
import NLA.TR06.Definitions

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped ENNReal MeasureTheory NNReal Topology Function
open MeasureTheory MeasureTheory.Measure Set Function Filter Metric

namespace NLA.TR06.Area

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {s : Set E} {f : E → F} {f' : E → E →L[ℝ] F}

local notation "ν" => (μHE[Module.finrank ℝ E] : Measure F)
local notation "μ" => (volume : Measure E)

omit [FiniteDimensional ℝ F] in
lemma image_measurable (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s) :
    MeasurableSet (f '' s) :=
  hs.image_of_continuousOn_injOn (fun x hx => (hf' x hx).continuousWithinAt) hf

/-- Both rectangular area inequalities, with a vanishing domain-volume error. -/
theorem area_estimates_aux (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfi : ∀ x ∈ s, Injective (f' x)) (hf : InjOn f s)
    {ε : ℝ≥0} (εpos : 0 < ε) :
    ν (f '' s) ≤ (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ) + 2 * ε * μ s ∧
    (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ) ≤ ν (f '' s) + 2 * ε * μ s := by
  classical
  rcases eq_empty_or_nonempty s with rfl | hsn
  · simp
  have hradius : ∀ A : E →L[ℝ] F, ∃ δ : ℝ≥0, 0 < δ ∧ (Injective A →
      (∀ B : E →L[ℝ] F, ‖B - A‖ ≤ δ →
        |B.toLinearMap.normDet - A.toLinearMap.normDet| ≤ ε) ∧
      (∀ (t : Set E) (g : E → F), ApproximatesLinearOn g A t δ →
        ν (g '' t) ≤ (ENNReal.ofReal A.toLinearMap.normDet + ε) * μ t) ∧
      (∀ (t : Set E) (g : E → F), ApproximatesLinearOn g A t δ →
        ENNReal.ofReal A.toLinearMap.normDet * μ t ≤ ν (g '' t) + ε * μ t)) := by
    intro A
    by_cases hA : Injective A
    · obtain ⟨δ, hp, hclose, hupper, hlower⟩ := exists_volume_radius A hA εpos
      exact ⟨δ, hp, fun _ => ⟨hclose, hupper, hlower⟩⟩
    · exact ⟨1, zero_lt_one, fun h => (hA h).elim⟩
  choose δ hδpos hδ using hradius
  obtain ⟨t, A, t_disj, t_meas, t_cover, ht, hsample⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt f s f' hf' δ
      (fun A => (hδpos A).ne')
  have hAi (n : ℕ) : Injective (A n) := by
    obtain ⟨y, hy, hAy⟩ := hsample hsn n
    rw [hAy]
    exact hfi y hy
  have s_eq : s = ⋃ n, s ∩ t n := by
    rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
  constructor
  · calc
      ν (f '' s) ≤ ν (⋃ n, f '' (s ∩ t n)) := by
        apply measure_mono
        rw [← image_iUnion, ← inter_iUnion]
        exact Set.image_mono (subset_inter Subset.rfl t_cover)
      _ ≤ ∑' n, ν (f '' (s ∩ t n)) := measure_iUnion_le _
      _ ≤ ∑' n, (ENNReal.ofReal (A n).toLinearMap.normDet + ε) * μ (s ∩ t n) := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        apply (hδ (A n) (hAi n)).2.1
        exact ht n
      _ = ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal (A n).toLinearMap.normDet + ε ∂μ := by
        simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter]
      _ ≤ ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal (f' x).toLinearMap.normDet + 2 * ε ∂μ := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        apply lintegral_mono_ae
        filter_upwards [approximation_norm_fderiv_sub_le μ (ht n) (hs.inter (t_meas n)) f' fun x hx =>
            (hf' x hx.1).mono inter_subset_left]
        intro x hx
        have I : (A n).toLinearMap.normDet ≤ (f' x).toLinearMap.normDet + ε := by
          have hb := (hδ (A n) (hAi n)).1 _ hx
          linarith [(abs_le.mp hb).1]
        calc
          ENNReal.ofReal (A n).toLinearMap.normDet + ε ≤ ENNReal.ofReal ((f' x).toLinearMap.normDet + ε) + ε := by gcongr
          _ = ENNReal.ofReal (f' x).toLinearMap.normDet + 2 * ε := by
            simp only [ENNReal.ofReal_add, LinearMap.normDet_nonneg, two_mul, add_assoc, NNReal.zero_le_coe,
              ENNReal.ofReal_coe_nnreal]
      _ = ∫⁻ x in ⋃ n, s ∩ t n, ENNReal.ofReal (f' x).toLinearMap.normDet + 2 * ε ∂μ := by
        have M : ∀ n : ℕ, MeasurableSet (s ∩ t n) := fun n => hs.inter (t_meas n)
        rw [lintegral_iUnion M]
        exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      _ = ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet + 2 * ε ∂μ := by
        rw [← inter_iUnion, inter_eq_self_of_subset_left t_cover]
      _ = (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ) + 2 * ε * μ s := by
        simp only [lintegral_add_right' _ aemeasurable_const, setLIntegral_const]
  · calc
      (∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ) =
          ∑' n, ∫⁻ x in s ∩ t n, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ := by
        conv_lhs => rw [s_eq]
        rw [lintegral_iUnion]
        · exact fun n => hs.inter (t_meas n)
        · exact pairwise_disjoint_mono t_disj fun n => inter_subset_right
      _ ≤ ∑' n, ∫⁻ _ in s ∩ t n, ENNReal.ofReal (A n).toLinearMap.normDet + ε ∂μ := by
        apply ENNReal.tsum_le_tsum fun n => ?_
        apply lintegral_mono_ae
        filter_upwards [approximation_norm_fderiv_sub_le μ (ht n) (hs.inter (t_meas n)) f' fun x hx =>
            (hf' x hx.1).mono inter_subset_left]
        intro x hx
        have I : (f' x).toLinearMap.normDet ≤ (A n).toLinearMap.normDet + ε := by
          have hb := (hδ (A n) (hAi n)).1 _ hx
          linarith [(abs_le.mp hb).2]
        calc
          ENNReal.ofReal (f' x).toLinearMap.normDet ≤ ENNReal.ofReal ((A n).toLinearMap.normDet + ε) :=
            ENNReal.ofReal_le_ofReal I
          _ = ENNReal.ofReal (A n).toLinearMap.normDet + ε := by
            simp only [ENNReal.ofReal_add, LinearMap.normDet_nonneg, NNReal.zero_le_coe, ENNReal.ofReal_coe_nnreal]
      _ = ∑' n, (ENNReal.ofReal (A n).toLinearMap.normDet * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
        simp only [setLIntegral_const, lintegral_add_right _ measurable_const]
      _ ≤ ∑' n, (ν (f '' (s ∩ t n)) + ε * μ (s ∩ t n) + ε * μ (s ∩ t n)) := by
        gcongr
        exact (hδ (A _) (hAi _)).2.2 _ _ (ht _)
      _ = ν (f '' s) + 2 * ε * μ s := by
        conv_rhs => rw [s_eq]
        rw [image_iUnion, measure_iUnion]; rotate_left
        · intro i j hij
          apply Disjoint.image _ hf inter_subset_left inter_subset_left
          exact Disjoint.mono inter_subset_right inter_subset_right (t_disj hij)
        · intro i
          exact
            image_measurable (hs.inter (t_meas i))
              (fun x hx => (hf' x hx.1).mono inter_subset_left)
              (hf.mono inter_subset_left)
        rw [measure_iUnion]; rotate_left
        · exact pairwise_disjoint_mono t_disj fun i => inter_subset_right
        · exact fun i => hs.inter (t_meas i)
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
        congr 1
        ext1 i
        rw [mul_assoc, two_mul, add_assoc]

/-- Exact area on a finite-volume measurable set for an injective immersion. -/
theorem area_finite (hs : MeasurableSet s) (hfinite : μ s ≠ ⊤)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfi : ∀ x ∈ s, Injective (f' x)) (hf : InjOn f s) :
    ν (f '' s) = ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ := by
  have hlim (a : ℝ≥0∞) :
      Tendsto (fun ε : ℝ≥0 => a + 2 * ε * μ s) (𝓝[>] 0) (𝓝 a) := by
    have h : Tendsto (fun ε : ℝ≥0 => a + 2 * ε * μ s) (𝓝[>] 0)
        (𝓝 (a + 2 * (0 : ℝ≥0) * μ s)) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      refine tendsto_const_nhds.add ?_
      refine ENNReal.Tendsto.mul_const ?_ (Or.inr hfinite)
      exact ENNReal.Tendsto.const_mul (ENNReal.tendsto_coe.2 tendsto_id)
        (Or.inr ENNReal.coe_ne_top)
    simpa only [add_zero, zero_mul, mul_zero, ENNReal.coe_zero] using h
  apply le_antisymm
  · apply ge_of_tendsto (hlim _)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (area_estimates_aux hs hf' hfi hf hε).1
  · apply ge_of_tendsto (hlim _)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (area_estimates_aux hs hf' hfi hf hε).2

/-- Rectangular area formula for an injective differentiable immersion on a
measurable set. Domain and codomain may have different finite dimensions. -/
theorem immersion_area (hs : MeasurableSet s)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    (hfi : ∀ x ∈ s, Injective (f' x)) (hf : InjOn f s) :
    ν (f '' s) = ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ := by
  let u n := disjointed (spanningSets μ) n
  have u_meas : ∀ n, MeasurableSet (u n) := by
    intro n
    apply MeasurableSet.disjointed fun i => ?_
    exact measurableSet_spanningSets μ i
  have A : s = ⋃ n, s ∩ u n := by
    rw [← inter_iUnion, iUnion_disjointed, iUnion_spanningSets, inter_univ]
  calc
    ν (f '' s) = ∑' n, ν (f '' (s ∩ u n)) := by
      conv_lhs => rw [A, image_iUnion]
      rw [measure_iUnion]
      · intro i j hij
        apply Disjoint.image _ hf inter_subset_left inter_subset_left
        exact Disjoint.mono inter_subset_right inter_subset_right
          (disjoint_disjointed _ hij)
      · intro i
        exact image_measurable (hs.inter (u_meas i))
          (fun x hx => (hf' x hx.1).mono inter_subset_left)
          (hf.mono inter_subset_left)
    _ = ∑' n, ∫⁻ x in s ∩ u n, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ := by
      congr 1
      funext n
      apply area_finite (hs.inter (u_meas n))
      · have hbound : μ (u n) < ⊤ :=
          lt_of_le_of_lt (measure_mono (disjointed_subset _ _))
            (measure_spanningSets_lt_top μ n)
        exact ne_of_lt (lt_of_le_of_lt (measure_mono inter_subset_right) hbound)
      · exact fun x hx => (hf' x hx.1).mono inter_subset_left
      · exact fun x hx => hfi x hx.1
      · exact hf.mono inter_subset_left
    _ = ∫⁻ x in s, ENNReal.ofReal (f' x).toLinearMap.normDet ∂μ := by
      conv_rhs => rw [A]
      rw [lintegral_iUnion]
      · intro n; exact hs.inter (u_meas n)
      · exact pairwise_disjoint_mono (disjoint_disjointed _) fun n => inter_subset_right

#print axioms immersion_area
#assert_trust kernel immersion_area

#print axioms area_estimates_aux
#assert_trust kernel area_estimates_aux

end NLA.TR06.Area

namespace NLA.TR06

/-- Euclidean Hausdorff volume is exactly the induced chart volume, with its
actual rectangular Jacobian. This is the unchanged reviewed Challenge target. -/
theorem induced_volume_chart {d : ℕ} {n : Fin d → ℕ} {r : ℕ}
    (c : DecompositionChart d n r)
    (s : Set (EuclideanSpace ℝ (Fin (expectedDimension d n r))))
    (hs : MeasurableSet s) (hsub : s ⊆ c.chart.source) :
    (μHE[expectedDimension d n r] : Measure (Tensor ℝ d n))
      ((fun v => (c.chart v).val) '' s) =
    ∫⁻ v in s,
      ENNReal.ofReal ((fderiv ℝ (fun w => (c.chart w).val) v).toLinearMap.normDet) := by
  have hf' : ∀ v ∈ s, HasFDerivWithinAt (fun w => (c.chart w).val)
      (fderiv ℝ (fun w => (c.chart w).val) v) s v := by
    intro v hv
    exact ((c.input_smooth.contDiffAt (c.chart.open_source.mem_nhds (hsub hv))).differentiableAt
      one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have hfi : ∀ v ∈ s, Function.Injective (fderiv ℝ (fun w => (c.chart w).val) v) :=
    fun v hv => c.input_injective_derivative v (hsub hv)
  have hf : Set.InjOn (fun v => (c.chart v).val) s := by
    intro x hx y hy hxy
    exact c.chart.injOn (hsub hx) (hsub hy) (Subtype.ext hxy)
  simpa only [finrank_euclideanSpace, Fintype.card_fin] using
    Area.immersion_area hs hf' hfi hf

#print axioms induced_volume_chart
#assert_trust kernel induced_volume_chart

end NLA.TR06
