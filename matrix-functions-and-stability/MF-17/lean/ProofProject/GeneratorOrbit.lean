import ProofProject.Laplace

/-! # Integrating generator orbits

Right derivatives suffice for the fundamental theorem of calculus, so no
extension to negative semigroup times is used.
-/

noncomputable section

namespace ProofProject

open Set Filter MeasureTheory
open scoped Topology

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A generator vector remains differentiable from the right along its orbit. -/
theorem GeneratorGraph.orbit_hasDerivWithinAt {T : StableSemigroup M H} {x y : H}
    (h : GeneratorGraph T x y) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => T.op s x) (T.op t y) (Ici t) t := by
  have hs : HasDerivWithinAt (fun s : ℝ => T.op (s - t) x) y (Ici t) t := by
    have hd := h.scomp_of_eq t ((hasDerivAt_id t).sub_const t).hasDerivWithinAt
      (show MapsTo (fun s : ℝ => s - t) (Ici t) (Ici 0) from
        fun s hs => show 0 ≤ s - t from sub_nonneg.mpr hs) (by simp)
    simpa only [Function.comp_def, id_eq, one_smul] using hd
  have hd := (T.op t).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivWithinAt t hs
  refine hd.congr ?_ ?_
  · intro s hs
    change T.op s x = T.op t (T.op (s - t) x)
    rw [← ContinuousLinearMap.comp_apply, ← T.add t (s - t) ht (sub_nonneg.mpr hs)]
    congr 2
    ring
  · change T.op t x = T.op t (T.op (t - t) x)
    simp [T.at_zero]

/-- The exponential stability bound sends every orbit to zero at infinity. -/
theorem StableSemigroup.orbit_tendsto_zero (T : StableSemigroup M H) (x : H) :
    Tendsto (fun t : ℝ => T.op t x) atTop (𝓝 0) := by
  have hb : Tendsto (fun t : ℝ => (M * Real.exp (-t)) * ‖x‖) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul M).mul_const ‖x‖
  apply squeeze_zero_norm' ?_ hb
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact ((T.op t).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (T.bound t ht) (norm_nonneg x))

variable [CompleteSpace H]

/-- Integrating a generator orbit gives the increment of the original orbit. -/
theorem GeneratorGraph.intervalIntegral_eq {T : StableSemigroup M H} {x y : H}
    (h : GeneratorGraph T x y) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, T.op s y) = T.op t x - x := by
  have hc : ContinuousOn (fun s : ℝ => T.op s x) (Icc 0 t) :=
    (T.strong_continuous x).mono fun _ hs => hs.1
  have hi : IntervalIntegrable (fun s : ℝ => T.op s y) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    exact (T.strong_continuous y).mono (by simpa only [uIcc_of_le ht] using Icc_subset_Ici_self)
  have hh := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hc
    (fun s hs => (h.orbit_hasDerivWithinAt hs.1.le).mono Ioi_subset_Ici_self) hi
  simpa only [T.at_zero, ContinuousLinearMap.id_apply] using hh

/-- The improper integral recovers the original vector from its generator. -/
theorem GeneratorGraph.integral_eq_neg {T : StableSemigroup M H} {x y : H}
    (h : GeneratorGraph T x y) :
    (∫ s in Ioi (0 : ℝ), T.op s y) = -x := by
  have hlim := intervalIntegral_tendsto_integral_Ioi (0 : ℝ) (T.integrable_orbit y) tendsto_id
  have hlim' : Tendsto (fun t : ℝ => ∫ s in (0 : ℝ)..t, T.op s y) atTop (𝓝 (-x)) := by
    have hz := (T.orbit_tendsto_zero x).sub_const x
    simp only [zero_sub] at hz
    apply hz.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (h.intervalIntegral_eq ht).symm
  exact tendsto_nhds_unique hlim hlim'

/-- The Laplace operator is a left inverse of the full generator graph. -/
theorem GeneratorGraph.laplaceInverse_eq {T : StableSemigroup M H} {x y : H}
    (h : GeneratorGraph T x y) : T.laplaceInverse y = x := by
  rw [StableSemigroup.laplaceInverse_apply, h.integral_eq_neg, neg_neg]

end ProofProject
