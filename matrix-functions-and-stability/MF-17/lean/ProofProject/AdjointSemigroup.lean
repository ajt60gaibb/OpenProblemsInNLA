import ProofProject.InverseGenerator

/-!
# Strong continuity of the adjoint semigroup

The Laplace inverse is injective, so the range of its adjoint is dense. Its
commutation and strong integral increment formula make adjoint orbits on that
range Lipschitz. The uniform semigroup bound extends continuity to every vector
by uniform approximation. No separability or operator-norm continuity is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProofProject

universe u

variable {M : ℝ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

namespace StableSemigroup

omit [CompleteSpace H] in
lemma bound_nonneg (T : StableSemigroup M H) : 0 ≤ M := by
  have h := (norm_nonneg (T.op 0)).trans (T.bound 0 le_rfl)
  simpa only [neg_zero, Real.exp_zero, mul_one] using h

omit [CompleteSpace H] in
lemma norm_op_le_bound (T : StableSemigroup M H) {t : ℝ} (ht : 0 ≤ t) :
    ‖T.op t‖ ≤ M := by
  exact (T.bound t ht).trans <| by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) T.bound_nonneg

/-- The strong Laplace inverse commutes with every nonnegative semigroup time. -/
lemma laplaceInverse_op_commute (T : StableSemigroup M H) (x : H)
    {t : ℝ} (ht : 0 ≤ t) :
    T.laplaceInverse (T.op t x) = T.op t (T.laplaceInverse x) := by
  simp only [laplaceInverse_apply, map_neg]
  rw [← (T.op t).integral_comp_comm (T.integrable_orbit x)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  change T.op s (T.op t x) = T.op t (T.op s x)
  rw [← ContinuousLinearMap.comp_apply, ← T.add s t hs.le ht,
    ← ContinuousLinearMap.comp_apply, ← T.add t s ht hs.le, add_comm s t]

/-- The inverse converts every orbit increment into a strong interval integral. -/
lemma laplaceInverse_op_sub (T : StableSemigroup M H) (x : H)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    T.laplaceInverse (T.op t x) - T.laplaceInverse (T.op s x) =
      ∫ v in s..t, T.op v x := by
  have hi (r : ℝ) (hr : 0 ≤ r) :
      IntervalIntegrable (fun v : ℝ => T.op v x) volume 0 r := by
    apply ContinuousOn.intervalIntegrable
    exact (T.strong_continuous x).mono
      (by simpa only [uIcc_of_le hr] using Icc_subset_Ici_self)
  calc
    T.laplaceInverse (T.op t x) - T.laplaceInverse (T.op s x) =
        (T.op t (T.laplaceInverse x) - T.laplaceInverse x) -
          (T.op s (T.laplaceInverse x) - T.laplaceInverse x) := by
      rw [T.laplaceInverse_op_commute x ht, T.laplaceInverse_op_commute x hs]
      abel
    _ = (∫ v in (0 : ℝ)..t, T.op v x) - ∫ v in (0 : ℝ)..s, T.op v x := by
      rw [T.laplaceInverse_orbit_sub x ht, T.laplaceInverse_orbit_sub x hs]
    _ = _ := intervalIntegral.integral_interval_sub_left (hi t ht) (hi s hs)

lemma norm_laplaceInverse_mul_op_sub_le (T : StableSemigroup M H)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    ‖T.laplaceInverse * (T.op t - T.op s)‖ ≤ M * |t - s| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg T.bound_nonneg (abs_nonneg _))
  intro x
  change ‖T.laplaceInverse (T.op t x - T.op s x)‖ ≤ (M * |t - s|) * ‖x‖
  rw [map_sub, T.laplaceInverse_op_sub x hs ht]
  calc
    ‖∫ v in s..t, T.op v x‖ ≤ (M * ‖x‖) * |t - s| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro v hv
      have hv0 : 0 ≤ v := (le_min hs ht).trans hv.1.le
      exact ((T.op v).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (T.norm_op_le_bound hv0) (norm_nonneg _))
    _ = _ := by ring

/-- Adjoint orbits are Lipschitz on the dense range of the adjoint inverse. -/
lemma adjoint_orbit_laplaceInverse_lipschitz (T : StableSemigroup M H) (x : H) :
    LipschitzOnWith (⟨M * ‖x‖, mul_nonneg T.bound_nonneg (norm_nonneg _)⟩ : ℝ≥0)
      (fun t : ℝ => star (T.op t) (star T.laplaceInverse x)) (Ici 0) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro t ht s hs
  simp only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk]
  calc
    ‖star (T.op t) (star T.laplaceInverse x) -
        star (T.op s) (star T.laplaceInverse x)‖ =
        ‖star (T.laplaceInverse * (T.op t - T.op s)) x‖ := by
      simp only [star_mul, star_sub, mul_apply_eq_comp, sub_apply]
    _ ≤ ‖star (T.laplaceInverse * (T.op t - T.op s))‖ * ‖x‖ :=
      (star (T.laplaceInverse * (T.op t - T.op s))).le_opNorm x
    _ ≤ (M * |t - s|) * ‖x‖ := by
      rw [norm_star]
      exact mul_le_mul_of_nonneg_right
        (T.norm_laplaceInverse_mul_op_sub_le hs ht) (norm_nonneg _)
    _ = (M * ‖x‖) * |t - s| := by ring

lemma denseRange_adjoint_laplaceInverse (T : StableSemigroup M H) :
    DenseRange (star T.laplaceInverse : H →L[ℂ] H) := by
  change Dense ((star T.laplaceInverse).range : Set H)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  rw [ContinuousLinearMap.star_eq_adjoint, ← ContinuousLinearMap.orthogonal_ker]
  have hk : T.laplaceInverse.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr T.isGeneratorInverse_laplaceInverse.injective
  rw [hk, Submodule.bot_orthogonal_eq_top]

/-- Strong continuity of the adjoint follows by uniform approximation from
the range of the adjoint inverse, even when the Hilbert space is nonseparable. -/
theorem adjoint_strong_continuous (T : StableSemigroup M H) (x : H) :
    ContinuousOn (fun t : ℝ => star (T.op t) x) (Ici 0) := by
  obtain ⟨xseq, hxseq, hxlim⟩ := mem_closure_iff_seq_limit.mp
    (T.denseRange_adjoint_laplaceInverse x)
  have hcts (n : ℕ) : ContinuousOn (fun t : ℝ => star (T.op t) (xseq n)) (Ici 0) := by
    obtain ⟨y, hy⟩ := hxseq n
    rw [← hy]
    exact (T.adjoint_orbit_laplaceInverse_lipschitz y).continuousOn
  have hunif : TendstoUniformlyOn (fun n t => star (T.op t) (xseq n))
      (fun t => star (T.op t) x) atTop (Ici 0) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Tendsto (fun n => M * ‖x - xseq n‖) atTop (𝓝 0) := by
      simpa only [sub_self, norm_zero, mul_zero] using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)).sub hxlim).norm.const_mul M
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn
    intro t ht
    calc
      dist (star (T.op t) x) (star (T.op t) (xseq n)) =
          ‖star (T.op t) (x - xseq n)‖ := by rw [dist_eq_norm, map_sub]
      _ ≤ ‖star (T.op t)‖ * ‖x - xseq n‖ := (star (T.op t)).le_opNorm _
      _ ≤ M * ‖x - xseq n‖ := by
        rw [norm_star]
        exact mul_le_mul_of_nonneg_right (T.norm_op_le_bound ht) (norm_nonneg _)
      _ < ε := hn
  exact hunif.continuousOn (Filter.Eventually.of_forall hcts).frequently

/-- The adjoint operators form a strongly continuous stable semigroup with
exactly the same exponential bound. -/
def adjoint (T : StableSemigroup M H) : StableSemigroup M H where
  op t := star (T.op t)
  at_zero := by simp [T.at_zero, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_id]
  add s t hs ht := by
    rw [add_comm s t, T.add t s ht hs]
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp]
  strong_continuous := T.adjoint_strong_continuous
  bound t ht := by simpa only [norm_star] using T.bound t ht

@[simp] lemma adjoint_op (T : StableSemigroup M H) (t : ℝ) :
    T.adjoint.op t = star (T.op t) := rfl

theorem adjoint_orbit_aestronglyMeasurable (T : StableSemigroup M H) (x : H) :
    AEStronglyMeasurable (fun t : ℝ => star (T.op t) x) (volume.restrict (Ioi 0)) :=
  ((T.adjoint_strong_continuous x).mono Ioi_subset_Ici_self).aestronglyMeasurable
    measurableSet_Ioi

theorem adjoint_orbit_integrable (T : StableSemigroup M H) (x : H) :
    IntegrableOn (fun t : ℝ => star (T.op t) x) (Ioi 0) :=
  T.adjoint.integrable_orbit x

end StableSemigroup

/-- A uniformly bounded strongly continuous semigroup also has strongly
continuous adjoint orbits. Damping it gives a stable semigroup, so no general
reflexive-space adjoint theorem or separability assumption is needed. -/
theorem boundedSemigroup_adjoint_strong_continuous
    (T : ℝ → H →L[ℂ] H)
    (hzero : T 0 = ContinuousLinearMap.id ℂ H)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    (hcts : ∀ x : H, ContinuousOn (fun t : ℝ => T t x) (Ici 0))
    (hbound : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ M) (x : H) :
    ContinuousOn (fun t : ℝ => star (T t) x) (Ici 0) := by
  let S : StableSemigroup M H :=
    { op := fun t => (Real.exp (-t) : ℂ) • T t
      at_zero := by simp [hzero]
      add := by
        intro s t hs ht
        rw [hadd s t hs ht, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul, smul_smul]
        simp only [neg_add, Real.exp_add, Complex.ofReal_mul]
      strong_continuous := by
        intro y
        exact (Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp continuous_neg)).continuousOn.smul (hcts y)
      bound := by
        intro t ht
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact (mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le).trans_eq
          (mul_comm _ _) }
  have hscalar : Continuous (fun t : ℝ => (Real.exp t : ℂ)) :=
    Complex.continuous_ofReal.comp Real.continuous_exp
  have heq (t : ℝ) : (Real.exp t : ℂ) • star (S.op t) x = star (T t) x := by
    change (Real.exp t : ℂ) • star ((Real.exp (-t) : ℂ) • T t) x = _
    simp only [star_smul, Complex.star_def, Complex.conj_ofReal,
      smul_apply, smul_smul]
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  exact (hscalar.continuousOn.smul (S.adjoint_strong_continuous x)).congr
    (fun t _ => (heq t).symm)

end ProofProject
