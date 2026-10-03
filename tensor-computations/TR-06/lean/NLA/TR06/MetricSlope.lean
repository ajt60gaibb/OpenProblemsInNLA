/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. Original mathematical proof: Matthew J. Colbrook.
-/
import NLA.TR06.Definitions
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators ENNReal MeasureTheory Topology
open MeasureTheory Set Filter

namespace NLA.TR06

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Reordering summands acts isometrically on the product Frobenius space. -/
def permuteAngular (σ : Equiv.Perm (Fin r)) :
    AngularOutput d n r ≃ₗᵢ[ℝ] AngularOutput d n r :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr σ.symm (Equiv.refl (TensorIndex d n)))

@[simp] theorem permuteAngular_apply (σ : Equiv.Perm (Fin r))
    (x : AngularOutput d n r) (q : Fin r × TensorIndex d n) :
    permuteAngular σ x q = x (σ q.1, q.2) := rfl

@[simp] theorem normalizedTuple_perm (a : Fin r → Tensor ℝ d n)
    (σ : Equiv.Perm (Fin r)) :
    normalizedTuple (a ∘ σ) = permuteAngular σ (normalizedTuple a) := by
  ext q
  rfl

theorem decomposes_perm {a : Fin r → Tensor ℝ d n} {A : Tensor ℝ d n}
    (ha : Decomposes a A) (σ : Equiv.Perm (Fin r)) : Decomposes (a ∘ σ) A := by
  refine ⟨fun i => ha.1 (σ i), ?_⟩
  simpa only [Function.comp_apply, Equiv.sum_comp] using ha.2

theorem edist_normalizedTuple_perm (a b : Fin r → Tensor ℝ d n)
    (σ : Equiv.Perm (Fin r)) :
    edist (normalizedTuple (a ∘ σ)) (normalizedTuple (b ∘ σ)) =
      edist (normalizedTuple a) (normalizedTuple b) := by
  simp only [normalizedTuple_perm, (permuteAngular σ).isometry.edist_eq]

/-- Identifiability reduces the choice-free infimum to a finite permutation
orbit, with either chosen ordering of the two inputs. -/
theorem angularDistance_eq_iInf_perm {A B : Tensor ℝ d n}
    {a b : Fin r → Tensor ℝ d n}
    (hA : Identifiable r A) (hB : Identifiable r B)
    (ha : Decomposes a A) (hb : Decomposes b B) :
    angularDistance r A B =
      ⨅ σ : Equiv.Perm (Fin r), edist (normalizedTuple a) (normalizedTuple (b ∘ σ)) := by
  apply le_antisymm
  · refine le_iInf fun σ => ?_
    exact iInf_le_of_le a (iInf_le_of_le ha
      (iInf_le_of_le (b ∘ σ) (iInf_le_of_le (decomposes_perm hb σ) le_rfl)))
  · unfold angularDistance
    refine le_iInf fun a' => le_iInf fun ha' => le_iInf fun b' => le_iInf fun hb' => ?_
    obtain ⟨σ, hσ⟩ := hA a a' ha ha'
    obtain ⟨τ, hτ⟩ := hB b b' hb hb'
    have ha'eq : a' = a ∘ σ := funext hσ
    have hb'eq : b' = b ∘ τ := funext hτ
    have hreduce :
        edist (normalizedTuple a') (normalizedTuple b') =
          edist (normalizedTuple a) (normalizedTuple (b ∘ (σ.symm.trans τ))) := by
      rw [← edist_normalizedTuple_perm a' b' σ.symm, ha'eq, hb'eq]
      congr 2
      ext i q
      simp
    rw [hreduce]
    exact iInf_le _ (σ.symm.trans τ)

/-- A finite isometry orbit has no local effect on distance from the base
point: stabilizers give exact equality, and the other orbit points stay apart. -/
theorem eventually_iInf_isometry_edist_eq {ι X Y : Type*} [Finite ι]
    [MetricSpace X] [TopologicalSpace Y] {u : Y} {f : Y → X}
    (e : ι → X ≃ᵢ X) (hid : ∃ i, ∀ x, e i x = x)
    (hf : ContinuousAt f u) :
    ∀ᶠ v in 𝓝 u, (⨅ i, edist (f u) (e i (f v))) = edist (f u) (f v) := by
  have hi : ∀ i, ∀ᶠ v in 𝓝 u, edist (f u) (f v) ≤ edist (f u) (e i (f v)) := by
    intro i
    by_cases hfix : e i (f u) = f u
    · filter_upwards [] with v
      simpa only [hfix] using (((e i).isometry.edist_eq (f u) (f v)).symm.le)
    · have hleft : ContinuousAt (fun v => edist (f u) (f v)) u :=
        continuousAt_const.edist hf
      have hright : ContinuousAt (fun v => edist (f u) (e i (f v))) u :=
        continuousAt_const.edist ((e i).continuous.continuousAt.comp hf)
      exact (hleft.eventually_lt hright (by simpa using edist_pos.mpr (Ne.symm hfix))).mono
        (fun _ h => h.le)
  filter_upwards [Filter.eventually_all.mpr hi] with v hv
  apply le_antisymm
  · obtain ⟨i, hi⟩ := hid
    exact (iInf_le _ i).trans_eq (by rw [hi])
  · exact le_iInf hv

/-- On a sufficiently small chart neighborhood, the unordered normalized
distance is exactly the distance in the given smooth normalized branch. -/
theorem eventually_angularDistance_eq_chart_edist
    (c : DecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    ∀ᶠ v in 𝓝 u,
      angularDistance r (c.chart u).val (c.chart v).val =
        edist (normalizedTuple (c.summands u)) (normalizedTuple (c.summands v)) := by
  have hsource : c.chart.source ∈ 𝓝 u := c.chart.open_source.mem_nhds hu
  have hcont : ContinuousAt (fun v => normalizedTuple (c.summands v)) u :=
    c.output_smooth.continuousOn.continuousAt hsource
  have horbit := eventually_iInf_isometry_edist_eq
    (fun σ : Equiv.Perm (Fin r) => (permuteAngular (d := d) (n := n) σ).toIsometryEquiv)
    (by refine ⟨Equiv.refl _, ?_⟩; intro x; ext q; rfl) hcont
  filter_upwards [hsource, horbit] with v hv hdist
  rw [angularDistance_eq_iInf_perm (c.chart u).property.2 (c.chart v).property.2
    (c.decomposes u hu) (c.decomposes v hv)]
  simpa only [normalizedTuple_perm, LinearIsometryEquiv.coe_toIsometryEquiv] using hdist

section DifferentialRatio

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {f : E → F} {g : E → G} {u : E} {f' : E →L[ℝ] F} {g' : E →L[ℝ] G}

/-- First-order bounds pass from two derivatives to the corresponding local
increments when the input derivative is injective. -/
theorem eventually_norm_sub_le_mul_norm_sub
    (hf : HasFDerivAt f f' u) (hg : HasFDerivAt g g' u)
    (hinj : Function.Injective f') {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ v, ‖g' v‖ ≤ C * ‖f' v‖) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ v in 𝓝 u, ‖g v - g u‖ ≤ (C + ε) * ‖f v - f u‖ := by
  obtain ⟨K, _, hK⟩ := f'.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hcoord : (fun v => v - u) =O[𝓝 u] (fun v => f v - f u) :=
    (hf.isTheta_sub (hK.isInducing f'.continuous)).symm.isBigO
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  have hferr := (hf.isLittleO.trans_isBigO hcoord).bound hδ
  have hgerr := (hg.isLittleO.trans_isBigO hcoord).bound hδ
  filter_upwards [hferr, hgerr] with v hvf hvg
  have h1 : ‖f' (v - u)‖ ≤ ‖f v - f u‖ + ‖f v - f u - f' (v - u)‖ :=
    norm_le_insert _ _
  have h2 : ‖g v - g u‖ ≤ ‖g' (v - u)‖ + ‖g v - g u - g' (v - u)‖ := by
    simpa only [norm_sub_rev] using (norm_le_insert (g' (v - u)) (g v - g u))
  have h3 := hbound (v - u)
  have h4 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add le_rfl hvf)) hC
  have hscale : (C + 1) * (ε / (C + 1)) = ε := by
    field_simp
  calc
    ‖g v - g u‖ ≤ C * (‖f v - f u‖ + ε / (C + 1) * ‖f v - f u‖) +
        ε / (C + 1) * ‖f v - f u‖ := h2.trans (add_le_add (h3.trans h4) hvg)
    _ = (C + (C + 1) * (ε / (C + 1))) * ‖f v - f u‖ := by ring
    _ = (C + ε) * ‖f v - f u‖ := by rw [hscale]

omit [FiniteDimensional ℝ E] in
/-- Directional difference quotients recover the ratio of the two
derivatives, without an approximation to either operator norm. -/
theorem tendsto_directional_norm_ratio
    (hf : HasFDerivAt f f' u) (hg : HasFDerivAt g g' u)
    (v : E) (hv : f' v ≠ 0) :
    Tendsto (fun t : ℝ => ENNReal.ofReal
      (‖g (u + t⁻¹ • v) - g u‖ / ‖f (u + t⁻¹ • v) - f u‖)) atTop
      (𝓝 (ENNReal.ofReal (‖g' v‖ / ‖f' v‖))) := by
  have hfl := hf.lim v (show Tendsto (fun t : ℝ => ‖t‖) atTop atTop from
    tendsto_norm_atTop_atTop)
  have hgl := hg.lim v (show Tendsto (fun t : ℝ => ‖t‖) atTop atTop from
    tendsto_norm_atTop_atTop)
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (hgl.norm.div hfl.norm (norm_ne_zero_iff.mpr hv))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp
  rw [norm_smul, norm_smul, mul_div_mul_left _ _ (norm_ne_zero_iff.mpr ht.ne')]

/-- The pointwise ratio slope of two differentiable maps is exactly the
supremum of their derivative ratios if the input derivative is injective. -/
theorem limsup_norm_ratio_eq_derivative_ratio
    (hf : HasFDerivAt f f' u) (hg : HasFDerivAt g g' u)
    (hinj : Function.Injective f') :
    limsup (fun v => ENNReal.ofReal (‖g v - g u‖ / ‖f v - f u‖)) (𝓝 u) =
      ⨆ v, ENNReal.ofReal (‖g' v‖ / ‖f' v‖) := by
  apply le_antisymm
  · let R : ℝ≥0∞ := ⨆ v, ENNReal.ofReal (‖g' v‖ / ‖f' v‖)
    change limsup _ _ ≤ R
    refine ENNReal.le_of_forall_pos_le_add fun ε hε hR => ?_
    have hlin : ∀ v, ‖g' v‖ ≤ R.toReal * ‖f' v‖ := by
      intro v
      by_cases hv : f' v = 0
      · have hv0 : v = 0 := hinj (by simpa using hv)
        simp [hv0]
      · have hb : ENNReal.ofReal (‖g' v‖ / ‖f' v‖) ≤ R :=
          le_iSup (fun w => ENNReal.ofReal (‖g' w‖ / ‖f' w‖)) v
        exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp
          ((ENNReal.ofReal_le_iff_le_toReal hR.ne).mp hb)
    have hε' : 0 < (ε : ℝ) := by exact_mod_cast hε
    have hlocal := eventually_norm_sub_le_mul_norm_sub hf hg hinj
      ENNReal.toReal_nonneg hlin hε'
    have hbound : ∀ᶠ v in 𝓝 u,
        ENNReal.ofReal (‖g v - g u‖ / ‖f v - f u‖) ≤
          ENNReal.ofReal (R.toReal + (ε : ℝ)) := by
      filter_upwards [hlocal] with v hv
      apply ENNReal.ofReal_le_ofReal
      by_cases hz : ‖f v - f u‖ = 0
      · simp only [hz, div_zero]
        positivity
      · exact (div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mpr hv
    calc
      limsup (fun v => ENNReal.ofReal (‖g v - g u‖ / ‖f v - f u‖)) (𝓝 u) ≤
          ENNReal.ofReal (R.toReal + (ε : ℝ)) := limsup_le_of_le (h := hbound)
      _ = R + ε := by
        rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ε.coe_nonneg,
          ENNReal.ofReal_toReal hR.ne, ENNReal.ofReal_coe_nnreal]
  · refine iSup_le fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hfv : f' v ≠ 0 := fun h => hv (hinj (by simpa using h))
    have hpath : Tendsto (fun t : ℝ => u + t⁻¹ • v) atTop (𝓝 u) := by
      simpa using tendsto_const_nhds.add
        (tendsto_inv_atTop_zero.smul (tendsto_const_nhds : Tendsto (fun _ : ℝ => v) atTop (𝓝 v)))
    refine le_limsup_of_le (h := ?_)
    intro b hb
    exact le_of_tendsto (tendsto_directional_norm_ratio hf hg v hfv) (hpath.eventually hb)

end DifferentialRatio

/-- Including the base point does not affect a nonnegative local supremum
when the value assigned to that point is zero. -/
theorem punctured_iInf_iSup_eq_limsup {X : Type*} [MetricSpace X]
    (s : Set X) (a : X) (h : X → ℝ≥0∞) (ha : h a = 0) :
    (⨅ (ε : ℝ) (_ : 0 < ε),
      ⨆ (b : X) (_ : b ∈ s) (_ : b ≠ a) (_ : dist a b < ε), h b) =
      limsup h (𝓝[s] a) := by
  rw [Metric.nhdsWithin_basis_ball.limsup_eq_iInf_iSup]
  congr 1
  funext ε
  congr 1
  funext hε
  apply le_antisymm
  · refine iSup_le fun b => iSup_le fun hb => iSup_le fun hba => iSup_le fun hdist => ?_
    exact le_iSup_of_le b (le_iSup_of_le ⟨by simpa [Metric.mem_ball, dist_comm] using hdist, hb⟩ le_rfl)
  · refine iSup_le fun b => iSup_le fun hb => ?_
    by_cases hba : b = a
    · simp [hba, ha]
    · exact le_iSup_of_le b (le_iSup_of_le hb.2 (le_iSup_of_le hba
        (le_iSup_of_le (by simpa [Metric.mem_ball, dist_comm] using hb.1) le_rfl)))

theorem angularDistance_self {A : Tensor ℝ d n}
    {a : Fin r → Tensor ℝ d n} (ha : Decomposes a A) : angularDistance r A A = 0 := by
  apply le_antisymm
  · calc
      angularDistance r A A ≤ edist (normalizedTuple a) (normalizedTuple a) :=
        iInf_le_of_le a (iInf_le_of_le ha
          (iInf_le_of_le a (iInf_le_of_le ha le_rfl)))
      _ = 0 := edist_self _
  · exact bot_le

theorem angularSlope_eq_limsup {A : Tensor ℝ d n}
    (hA : A ∈ identifiableRealSet d n r) :
    angularSlope r A = limsup (fun B => angularDistance r A B / edist A B)
      (𝓝[identifiableRealSet d n r] A) := by
  obtain ⟨a, ha⟩ := hA.1.1
  exact punctured_iInf_iSup_eq_limsup _ _ _ (by simp [angularDistance_self ha])

/-- The order-free angular metric slope is the derivative ratio of any
legitimate local embedded decomposition chart. -/
theorem angularSlope_eq_chart_derivative
    (c : DecompositionChart d n r)
    (u : EuclideanSpace ℝ (Fin (expectedDimension d n r))) (hu : u ∈ c.chart.source) :
    angularSlope r (c.chart u).val =
      derivativeRatio (fderiv ℝ (fun v => (c.chart v).val) u)
        (fderiv ℝ (fun v => normalizedTuple (c.summands v)) u) := by
  have hsource : c.chart.source ∈ 𝓝 u := c.chart.open_source.mem_nhds hu
  have hf := ((c.input_smooth.differentiableOn (by norm_num)).differentiableAt hsource).hasFDerivAt
  have hg := ((c.output_smooth.differentiableOn (by norm_num)).differentiableAt hsource).hasFDerivAt
  have hmap : map (fun v => (c.chart v).val) (𝓝 u) =
      𝓝[identifiableRealSet d n r] (c.chart u).val := by
    change map (Subtype.val ∘ c.chart) (𝓝 u) = _
    rw [← map_map, c.chart.map_nhds_eq hu, map_nhds_subtype_val]
  rw [angularSlope_eq_limsup (c.chart u).property, ← hmap, ← limsup_comp]
  have hdist := eventually_angularDistance_eq_chart_edist c u hu
  have hratio : ∀ᶠ v in 𝓝 u,
      angularDistance r (c.chart u).val (c.chart v).val /
          edist (c.chart u).val (c.chart v).val =
      ENNReal.ofReal (‖normalizedTuple (c.summands v) - normalizedTuple (c.summands u)‖ /
          ‖(c.chart v).val - (c.chart u).val‖) := by
    filter_upwards [hsource, hdist] with v hv hdistv
    rw [hdistv]
    by_cases hvu : (c.chart v).val = (c.chart u).val
    · have heq : v = u := c.chart.injOn hv hu (Subtype.val_injective hvu)
      simp [heq]
    · simp only [edist_dist, dist_eq_norm']
      exact (ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hvu))).symm
  simp only [Function.comp_def]
  rw [limsup_congr hratio]
  exact limsup_norm_ratio_eq_derivative_ratio hf hg (c.input_injective_derivative u hu)

end NLA.TR06

#print axioms NLA.TR06.angularSlope_eq_chart_derivative
#assert_trust kernel NLA.TR06.angularSlope_eq_chart_derivative
