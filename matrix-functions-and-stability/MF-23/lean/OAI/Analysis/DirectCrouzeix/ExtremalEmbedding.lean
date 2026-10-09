/-
Portions of this file have been adapted from an external source.
The source copyright header and license information are preserved below.
-/

import OAI.Analysis.DirectCrouzeix.NormalFamilies

namespace OAI

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

noncomputable section

open Filter Metric Set

open scoped Topology ComplexConjugate

namespace DirectCrouzeix

namespace Conformal

open Function Complex

open scoped Pointwise

/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

The following conformal embedding declarations are adapted from Mathlib.Analysis.Complex.RiemannMapping.
Source: https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Complex/RiemannMapping.lean

This code has been modified.
-/

theorem exists_injective_not_dense_image_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, Injective f ∧ ¬Dense (f '' U) ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  wlog hU₀ : 0 ∉ U
  · rw [ne_univ_iff_exists_notMem] at hU
    rcases hU with ⟨a, ha⟩
    specialize this (hUo.vadd (-a)) (by simpa) (by simp [hU])
      (by simpa [mem_vadd_set_iff_neg_vadd_mem])
    rcases this with ⟨f, hf_inj, hf_dense, hdf⟩
    refine ⟨f ∘ (-a + ·), hf_inj.comp (add_right_injective (-a)), ?_, fun z hz ↦ ?_⟩
    · simpa only [← image_vadd, Set.image_image] using! hf_dense
    · simpa [Function.comp_def, deriv_comp_const_add] using hdf (-a + z) (mapsTo_image _ _ hz)

  rcases exists_continuousOn_pow_eq hUc hUo continuousOn_id (by rwa [image_id]) two_ne_zero
    with ⟨f, hfc, hf_inv⟩
  replace hf_inv : LeftInverse (· ^ 2) f := hf_inv

  have hf₀ : ∀ z ∈ U, f z ≠ 0 := by
    intro z hz hfz
    simpa [hfz, (ne_of_mem_of_not_mem hz hU₀).symm] using hf_inv z

  have hdf : ∀ z ∈ U, HasStrictDerivAt f (2 * f z)⁻¹ z := by
    intro z hz
    apply HasStrictDerivAt.of_local_left_inverse
    · exact hfc.continuousAt <| hUo.mem_nhds hz
    · simpa using hasStrictDerivAt_pow 2 (f z)
    · simpa using hf₀ z hz
    · exact .of_forall hf_inv

  refine ⟨f, hf_inv.injective, ?_, fun z hz ↦ ?_⟩
  ·
    simp only [Dense, not_forall, mem_closure_iff_frequently, not_frequently]
    rcases hUc.nonempty with ⟨x, hx⟩

    use -f x

    have : f '' U ∈ 𝓝 (f x) := by
      rw [← (hdf x hx).map_nhds_eq (by simpa using hf₀ x hx)]
      exact Filter.image_mem_map <| hUo.mem_nhds hx

    rw [nhds_neg, eventually_neg]

    filter_upwards [this]
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    obtain rfl : a = b := by
      rw [← hf_inv b, hab]
      simp [hf_inv a]
    refine hf₀ a ha ?_
    linear_combination hab / 2
  · simpa [(hdf z hz).hasDerivAt.deriv] using hf₀ z hz

lemma exists_mapsTo_unitBall_injOn_deriv_ne_zero {U : Set ℂ} (hUo : IsOpen U)
    (hUc : IsSimplyConnected U) (hU : U ≠ univ) :
    ∃ f : ℂ → ℂ, MapsTo f U (ball 0 1) ∧ InjOn f U ∧ ∀ z ∈ U, deriv f z ≠ 0 := by

  rcases exists_injective_not_dense_image_deriv_ne_zero hUo hUc hU with ⟨f, hf_inj, hfd, hdf⟩

  obtain ⟨x, ε, hε₀, hε⟩ : ∃ (x : ℂ) (ε : ℝ), 0 < ε ∧ ∀ a ∈ U, ε < dist (f a) x := by
    simpa [Dense, mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall] using hfd
  have hfx : ∀ z ∈ U, f z ≠ x := fun z hz ↦ by simpa using hε₀.trans (hε z hz)

  use fun z ↦ ε / (f z - x)
  refine ⟨?mapsTo, ?injOn, ?deriv⟩
  case mapsTo =>
    intro z hz
    rw [mem_ball_zero_iff, norm_div, norm_real, Real.norm_of_nonneg hε₀.le, div_lt_one₀]
    · simpa [dist_eq_norm] using hε z hz
    · simpa [sub_eq_zero] using hfx z hz
  case injOn =>
    intro z hz w hw heq
    simpa [div_eq_mul_inv, hε₀.ne', hf_inj.eq_iff] using heq
  case deriv =>
    intro z hz
    have hdz : DifferentiableAt ℂ f z := differentiableAt_of_deriv_ne_zero (hdf z hz)
    rw [(hasDerivAt_const _ _).fun_div (hdz.hasDerivAt.sub_const _) _ |>.deriv] <;>
      simp [*, ne_of_gt, sub_eq_zero]

structure NormalizedEmbedding (U : Set ℂ) (a : ℂ) (f : ℂ → ℂ) : Prop where
  holomorphic : DifferentiableOn ℂ f U
  disk : MapsTo f U (ball 0 1)
  injective : InjOn f U
  derivative : ∀ z ∈ U, deriv f z ≠ 0
  normalized : f a = 0

theorem exists_normalizedEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f := by
  obtain ⟨e, hed, hei, he'⟩ :=
    exists_mapsTo_unitBall_injOn_deriv_ne_zero hU hUc hproper
  have he : DifferentiableOn ℂ e U := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (he' z hz)).differentiableWithinAt
  let f : ℂ → ℂ := fun z => (e z - e a) / 2
  have hf' (z : ℂ) (hz : z ∈ U) : HasDerivAt f (deriv e z / 2) z :=
    ((he.hasDerivAt (hU.mem_nhds hz)).sub_const _).div_const _
  refine ⟨f, ⟨he.sub_const _ |>.div_const _, ?_, ?_, ?_, by simp [f]⟩⟩
  · intro z hz
    rw [mem_ball_zero_iff]
    dsimp [f]
    rw [norm_div]
    norm_num
    have h1 := norm_sub_le (e z) (e a)
    have h2 : ‖e z‖ < 1 := mem_ball_zero_iff.mp (hed hz)
    have h3 : ‖e a‖ < 1 := mem_ball_zero_iff.mp (hed ha)
    linarith
  · intro z hz w hw heq
    apply hei hz hw
    dsimp [f] at heq
    exact sub_left_injective ((div_left_inj' (by norm_num : (2 : ℂ) ≠ 0)).mp heq)
  · intro z hz
    rw [(hf' z hz).deriv]
    exact div_ne_zero (he' z hz) (by norm_num)

theorem extend_restrict_eventuallyEq {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} {a : ℂ} (ha : a ∈ U) :
    extend U (fun z : U => f z) =ᶠ[𝓝 a] f := by
  filter_upwards [hU.mem_nhds ha] with z hz
  simp [extend, hz]

theorem exists_extremalEmbedding {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsSimplyConnected U) (hproper : U ≠ univ) {a : ℂ} (ha : a ∈ U) :
    ∃ f, NormalizedEmbedding U a f ∧
      ∀ g, NormalizedEmbedding U a g → ‖deriv g a‖ ≤ ‖deriv f a‖ := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let S : Set C(U, ℂ) := {f | NormalizedEmbedding U a (extend U f)}
  have hS : ∀ f ∈ S, DifferentiableOn ℂ (extend U f) U ∧ ∀ z : U, ‖f z‖ ≤ 1 := by
    intro f hf
    refine ⟨hf.holomorphic, fun z => ?_⟩
    simpa only [extend_coe] using (mem_ball_zero_iff.mp (hf.disk z.property)).le
  have hCS := bounded_holomorphic_compact hU S hS
  have hLS (g : C(U, ℂ)) (hg : g ∈ closure S) := bounded_holomorphic_closure hU hS hg
  have hmk (f : ℂ → ℂ) (hf : NormalizedEmbedding U a f) :
      (⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩ : C(U, ℂ)) ∈ S := by
    let g : C(U, ℂ) := ⟨fun z : U => f z, hf.holomorphic.continuousOn.domRestrict⟩
    have heq (z : ℂ) (hz : z ∈ U) : extend U g =ᶠ[𝓝 z] f :=
      extend_restrict_eventuallyEq hU hz
    change NormalizedEmbedding U a (extend U g)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      exact ((hf.holomorphic.differentiableAt (hU.mem_nhds hz)).congr_of_eventuallyEq
        (heq z hz)).differentiableWithinAt
    · intro z hz
      rw [(heq z hz).self_of_nhds]
      exact hf.disk hz
    · intro z hz w hw he
      apply hf.injective hz hw
      rwa [(heq z hz).self_of_nhds, (heq w hw).self_of_nhds] at he
    · intro z hz
      rw [(heq z hz).deriv_eq]
      exact hf.derivative z hz
    · rw [(heq a ha).self_of_nhds]
      exact hf.normalized
  obtain ⟨f₀, hf₀⟩ := exists_normalizedEmbedding hU hUc hproper ha
  let F₀ : C(U, ℂ) := ⟨fun z : U => f₀ z, hf₀.holomorphic.continuousOn.domRestrict⟩
  have hF₀ : F₀ ∈ S := hmk _ hf₀
  obtain ⟨g, hg, hmax⟩ := hCS.exists_isMaxOn ⟨F₀, subset_closure hF₀⟩
    (derivative_continuousOn hU (fun f hf => (hLS _ hf).1) ha).norm
  have hpos : 0 < ‖deriv (extend U g) a‖ :=
    (norm_pos_iff.mpr (hF₀.derivative a ha)).trans_le (hmax (subset_closure hF₀))
  obtain ⟨F, hF, hl⟩ := mem_closure_iff_seq_limit.mp hg
  have hlu := continuousMap_limit hU hl
  have hd := (hLS _ hg).1
  have hn : extend U g a = 0 := by
    exact tendsto_nhds_unique (hlu.tendsto_at ha)
      (by simpa only [(hF _).normalized] using tendsto_const_nhds (x := (0 : ℂ)))
  have hi : InjOn (extend U g) U := by
    apply (constant_or_injective_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => (hF n).holomorphic) (fun n => (hF n).injective) hlu).resolve_left
    rintro ⟨c, hc⟩
    have he : extend U g =ᶠ[𝓝 a] (fun _ => c) := by
      filter_upwards [hU.mem_nhds ha] with z hz
      exact hc hz
    have hz := he.deriv_eq
    simp only [deriv_const] at hz
    exact (ne_of_gt hpos) (by rw [hz, norm_zero])
  have hder : ∀ z ∈ U, deriv (extend U g) z ≠ 0 := by
    have hdl := hlu.deriv (Eventually.of_forall (fun n => (hF n).holomorphic)) hU
    apply (zero_or_nonvanishing_limit hU hUc.isPathConnected.isConnected.isPreconnected
      (fun n => ((hF n).holomorphic.analyticOnNhd hU).deriv.differentiableOn)
      (fun n => (hF n).derivative) hdl).resolve_left
    intro he
    exact (ne_of_gt hpos) (by rw [he ha, Pi.zero_apply, norm_zero])
  have hgN : NormalizedEmbedding U a (extend U g) :=
    ⟨hd, strict_bound_of_normalized hU hUc.isPathConnected.isConnected.isPreconnected hd
      (fun z hz => by simpa [extend, hz] using (hLS _ hg).2 ⟨z, hz⟩) ha hn, hi, hder, hn⟩
  refine ⟨extend U g, hgN, fun f hf => ?_⟩
  have hm := hmax (subset_closure (hmk f hf))
  change ‖deriv (extend U (fun z : U => f z)) a‖ ≤ _ at hm
  rwa [(extend_restrict_eventuallyEq hU ha).deriv_eq] at hm

end Conformal

end DirectCrouzeix

end

end

end

end OAI
