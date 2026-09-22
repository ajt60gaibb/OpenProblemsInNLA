import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-!
Finite-product variance tensorization, with all measurability and boundedness
hypotheses explicit. The proof uses variance decomposition and scalar Jensen;
no Poincare or tensorization inequality is assumed.
Original application: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace NLA.IE22

private theorem vt_memLp {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : MemLp f 2 μ :=
  MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

private theorem vt_integrable {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : Integrable f μ :=
  (vt_memLp μ hf C hb).integrable (by norm_num)

private theorem vt_integral_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) : ‖∫ x, f x ∂μ‖ ≤ C := by
  simpa using norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

private theorem vt_sq_integral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h := variance_nonneg f μ
  rw [variance_eq_sub hf] at h
  simpa only [Pi.pow_apply] using (sub_nonneg.mp h)

private theorem vt_variance_right_measurable {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {f : α × β → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Measurable (fun x => Var[fun y => f (x, y); ν]) := by
  have heq (x : α) : Var[fun y => f (x,y); ν] =
      (∫ y, f (x,y) ^ 2 ∂ν) - (∫ y, f (x,y) ∂ν) ^ 2 := by
    exact variance_eq_sub (vt_memLp ν (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hb (x,y)))
  simp_rw [heq]
  exact ((hf.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable).sub
    (hf.stronglyMeasurable.integral_prod_right'.measurable.pow_const 2)

private theorem vt_variance_right_bound {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (ν : Measure β) [IsProbabilityMeasure ν] {f : α × β → ℝ}
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (x : α) :
    ‖Var[fun y => f (x, y); ν]‖ ≤ C ^ 2 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (variance_nonneg _ _)]
  refine (variance_le_expectation_sq
    (hf.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).trans ?_
  have hs (y : β) : f (x,y) ^ 2 ≤ C ^ 2 := by
    have h := hb (x,y)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h 2
  have hi := (vt_memLp ν (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hb (x,y))).integrable_sq
  simpa using integral_mono hi (integrable_const (C ^ 2)) hs

/-- Variance decomposition for a bounded measurable function on two independent factors. -/
theorem bounded_variance_prod_decomposition {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; μ.prod ν] = (∫ x, Var[fun y => f (x,y); ν] ∂μ) +
      Var[fun x => ∫ y, f (x,y) ∂ν; μ] := by
  have hF := vt_memLp (μ.prod ν) hf C hb
  have hM : MemLp (fun x => ∫ y, f (x,y) ∂ν) 2 μ :=
    vt_memLp μ hf.stronglyMeasurable.integral_prod_right'.measurable C
      (fun x => vt_integral_bound ν C (fun y => hb (x,y)))
  have heq (x : α) : Var[fun y => f (x,y); ν] =
      (∫ y, f (x,y) ^ 2 ∂ν) - (∫ y, f (x,y) ∂ν) ^ 2 := by
    exact variance_eq_sub (vt_memLp ν (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hb (x,y)))
  simp_rw [heq]
  rw [integral_sub hF.integrable_sq.integral_prod_left hM.integrable_sq,
    variance_eq_sub hM, variance_eq_sub hF]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hF.integrable_sq, integral_prod _ (hF.integrable (by norm_num))]
  ring

/-- Averaging over an independent factor contracts the variance. -/
theorem bounded_variance_integral_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[fun x => ∫ y, f (x,y) ∂ν; μ] ≤ ∫ y, Var[fun x => f (x,y); μ] ∂ν := by
  let a : β → ℝ := fun y => ∫ x, f (x,y) ∂μ
  have ha : Measurable a := hf.stronglyMeasurable.integral_prod_left'.measurable
  have hab (y : β) : ‖a y‖ ≤ C := vt_integral_bound μ C (fun x => hb (x,y))
  let q : α × β → ℝ := fun z => f z - a z.2
  have hq : Measurable q := hf.sub (ha.comp measurable_snd)
  have hqb (z : α × β) : ‖q z‖ ≤ C + C :=
    (norm_sub_le _ _).trans (add_le_add (hb z) (hab z.2))
  have hQ := vt_memLp (μ.prod ν) hq (C+C) hqb
  have hF := vt_memLp (μ.prod ν) hf C hb
  have hA := vt_integrable ν ha C hab
  have hmean : (∫ y, a y ∂ν) = ∫ x, ∫ y, f (x,y) ∂ν ∂μ :=
    (integral_integral_swap (f := fun x y => f (x,y)) (hF.integrable (by norm_num))).symm
  have hinner (x : α) : (∫ y, q (x,y) ∂ν) =
      (∫ y, f (x,y) ∂ν) - ∫ x, ∫ y, f (x,y) ∂ν ∂μ := by
    dsimp [q]
    have hfx : Integrable (fun y => f (x,y)) ν :=
      vt_integrable ν (hf.comp (measurable_const.prodMk measurable_id)) C (fun y => hb (x,y))
    rw [integral_sub hfx hA, hmean]
  have hMQ := vt_memLp μ hq.stronglyMeasurable.integral_prod_right'.measurable (C+C)
    (fun x => vt_integral_bound ν (C+C) (fun y => hqb (x,y)))
  rw [variance_eq_integral hf.stronglyMeasurable.integral_prod_right'.aemeasurable]
  simp_rw [← hinner]
  calc
    _ ≤ ∫ x, ∫ y, q (x,y) ^ 2 ∂ν ∂μ := by
      apply integral_mono hMQ.integrable_sq hQ.integrable_sq.integral_prod_left
      intro x
      exact vt_sq_integral_le ν (vt_memLp ν
        (hq.comp (measurable_const.prodMk measurable_id)) (C+C) (fun y => hqb (x,y)))
    _ = ∫ y, ∫ x, q (x,y) ^ 2 ∂μ ∂ν := integral_integral_swap hQ.integrable_sq
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have hfy : AEMeasurable (fun x => f (x,y)) μ :=
        (hf.comp (measurable_id.prodMk measurable_const)).aemeasurable
      rw [variance_eq_integral hfy]

/-- The two-factor variance inequality, with its exact unit constants. -/
theorem bounded_variance_prod_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; μ.prod ν] ≤ (∫ x, Var[fun y => f (x,y); ν] ∂μ) +
      ∫ y, Var[fun x => f (x,y); μ] ∂ν := by
  rw [bounded_variance_prod_decomposition μ ν f hf C hb]
  exact add_le_add le_rfl (bounded_variance_integral_le μ ν f hf C hb)

private theorem vt_cons_preserving (μ : Measure ℝ) [IsProbabilityMeasure μ] (d : ℕ) :
    MeasurePreserving (fun z : ℝ × (Fin d → ℝ) => Fin.cons z.1 z.2)
      (μ.prod (Measure.pi (fun _ : Fin d => μ)))
      (Measure.pi (fun _ : Fin (d+1) => μ)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    (measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => μ) 0).symm

private theorem vt_measurable_cons (d : ℕ) :
    Measurable (fun z : ℝ × (Fin d → ℝ) => (Fin.cons z.1 z.2 : Fin (d+1) → ℝ)) := by
  exact (vt_cons_preserving (gaussianReal 0 1) d).measurable

private theorem vt_measurable_update {d : ℕ} (i : Fin d) :
    Measurable (fun z : (Fin d → ℝ) × ℝ => Function.update z.1 i z.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases h : j = i
  · subst j
    simpa using measurable_snd
  · simpa [Function.update_of_ne h, Function.comp_def] using (measurable_pi_apply j).comp measurable_fst

private theorem vt_coordinate_variance_measurable {d : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (i : Fin d) :
    Measurable (fun x => Var[fun t => f (Function.update x i t); μ]) := by
  apply vt_variance_right_measurable (α := Fin d → ℝ) (β := ℝ) μ
    (f := fun z : (Fin d → ℝ) × ℝ => f (Function.update z.1 i z.2)) _ C
  · exact fun z => hb (Function.update z.1 i z.2)
  · exact hf.comp (vt_measurable_update i)

private theorem vt_coordinate_variance_integrable {d : ℕ}
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (i : Fin d) :
    Integrable (fun x => Var[fun t => f (Function.update x i t); μ])
      (Measure.pi (fun _ : Fin d => μ)) :=
  vt_integrable _ (vt_coordinate_variance_measurable μ f hf C hb i) (C^2)
    (fun x => vt_variance_right_bound (α := Fin d → ℝ) (β := ℝ) μ
      (f := fun z : (Fin d → ℝ) × ℝ => f (Function.update z.1 i z.2))
      (hf.comp (vt_measurable_update i)) C (fun z => hb (Function.update z.1 i z.2)) x)

private theorem vt_integral_cons (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (f : (Fin (d+1) → ℝ) → ℝ) :
    (∫ x, f x ∂Measure.pi (fun _ : Fin (d+1) => μ)) =
      ∫ z : ℝ × (Fin d → ℝ), f (Fin.cons z.1 z.2)
        ∂μ.prod (Measure.pi (fun _ : Fin d => μ)) := by
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq] using
    (((measurePreserving_piFinSuccAbove (fun _ : Fin (d+1) => μ) 0).symm).integral_comp' f).symm

/-- Variance tensorization for a finite product of copies of a probability law.
Pointwise boundedness makes every displayed section variance and integral finite. -/
theorem bounded_variance_pi (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) :
    Var[f; Measure.pi (fun _ : Fin d => μ)] ≤
      ∑ i : Fin d, ∫ x, Var[fun t => f (Function.update x i t); μ]
        ∂Measure.pi (fun _ : Fin d => μ) := by
  induction d with
  | zero =>
      have heq : f = fun _ => f (fun i => Fin.elim0 i) := by
        funext x
        congr 1
        exact Subsingleton.elim _ _
      rw [heq]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rw [variance_eq_integral aemeasurable_const]
      simp
  | succ d ih =>
      let π : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => μ)
      let F : ℝ × (Fin d → ℝ) → ℝ := fun z => f (Fin.cons z.1 z.2)
      have hF : Measurable F := hf.comp (vt_measurable_cons d)
      have hFb (z : ℝ × (Fin d → ℝ)) : ‖F z‖ ≤ C := hb _
      let V : Fin (d+1) → ℝ × (Fin d → ℝ) → ℝ :=
        fun i z => Var[fun t => f (Function.update (Fin.cons z.1 z.2) i t); μ]
      have hVm (i : Fin (d+1)) : Measurable (V i) :=
        (vt_coordinate_variance_measurable μ f hf C hb i).comp (vt_measurable_cons d)
      have hVb (i : Fin (d+1)) (z : ℝ × (Fin d → ℝ)) : ‖V i z‖ ≤ C^2 :=
        vt_variance_right_bound (α := Fin (d+1) → ℝ) (β := ℝ) μ
          (f := fun p : (Fin (d+1) → ℝ) × ℝ => f (Function.update p.1 i p.2))
          (hf.comp (vt_measurable_update i)) C (fun p => hb _) _
      have hVi (i : Fin (d+1)) : Integrable (V i) (μ.prod π) :=
        vt_integrable _ (hVm i) (C^2) (hVb i)
      have hsum : Integrable (fun a => ∑ i : Fin d, ∫ y, V i.succ (a,y) ∂π) μ := by
        exact integrable_finsetSum _ fun i _ => (hVi i.succ).integral_prod_left
      have hsplit : (∑ i : Fin (d+1), ∫ x,
          Var[fun t => f (Function.update x i t); μ]
            ∂Measure.pi (fun _ : Fin (d+1) => μ)) =
          (∫ y, Var[fun a => F (a,y); μ] ∂π) +
            ∫ a, ∑ i : Fin d, ∫ y, V i.succ (a,y) ∂π ∂μ := by
        rw [Fin.sum_univ_succ]
        congr 1
        · rw [vt_integral_cons μ d]
          change (∫ z, V 0 z ∂μ.prod π) = _
          rw [integral_prod _ (hVi 0)]
          simp [V, F, Fin.update_cons_zero]
        · rw [integral_finsetSum _ (fun i _ => (hVi i.succ).integral_prod_left)]
          apply Finset.sum_congr rfl
          intro i _
          rw [vt_integral_cons μ d]
          exact integral_prod _ (hVi i.succ)
      have hsection (a : ℝ) : Var[fun y => F (a,y); π] ≤
          ∑ i : Fin d, ∫ y, V i.succ (a,y) ∂π := by
        have hm : Measurable (fun y => F (a,y)) :=
          hF.comp (measurable_const.prodMk measurable_id)
        simpa only [F, V, Fin.cons_update] using
          ih (fun y => F (a,y)) hm (fun y => hFb (a,y))
      have hleft : Integrable (fun a => Var[fun y => F (a,y); π]) μ :=
        vt_integrable μ (vt_variance_right_measurable π hF C hFb) (C^2)
          (vt_variance_right_bound π hF C hFb)
      rw [hsplit]
      have hv : Var[f; Measure.pi (fun _ : Fin (d+1) => μ)] = Var[F; μ.prod π] :=
        ((vt_cons_preserving μ d).variance_fun_comp hf.aemeasurable).symm
      rw [hv]
      refine (bounded_variance_prod_le μ π F hF C hFb).trans ?_
      simpa only [add_comm] using
        (add_le_add (integral_mono hleft hsum hsection)
          (le_refl (∫ y, Var[fun a => F (a,y); μ] ∂π)))

/-- The exact Gaussian product specialization used for the bounded projected hinge.
No independence of the correlated projected rows is required. -/
theorem gaussian_variance_tensorization (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
    Var[f; Measure.pi (fun _ : Fin d => gaussianReal 0 1)] ≤
      ∑ i : Fin d, ∫ x, Var[fun t => f (Function.update x i t); gaussianReal 0 1]
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  obtain ⟨C, hC⟩ := hbounded
  exact bounded_variance_pi (gaussianReal 0 1) d f hf C (by simpa only [Real.norm_eq_abs] using hC)

/-- Integrability of the coordinate variances used when integrating scalar
Gaussian Poincare bounds. This also excludes default integral values. -/
theorem gaussian_coordinate_variance_integrable (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) (i : Fin d) :
    Integrable (fun x => Var[fun t => f (Function.update x i t); gaussianReal 0 1])
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  obtain ⟨C, hC⟩ := hbounded
  exact vt_coordinate_variance_integrable (gaussianReal 0 1) f hf C
    (by simpa only [Real.norm_eq_abs] using hC) i

/-- Resampling one coordinate preserves the integral under a product law. -/
theorem bounded_integral_coordinate_resampling (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (d : ℕ) (f : (Fin d → ℝ) → ℝ) (hf : Measurable f)
    (C : ℝ) (hb : ∀ x, ‖f x‖ ≤ C) (i : Fin d) :
    (∫ x, ∫ t, f (Function.update x i t) ∂μ
      ∂Measure.pi (fun _ : Fin d => μ)) =
        ∫ x, f x ∂Measure.pi (fun _ : Fin d => μ) := by
  cases d with
  | zero => exact Fin.elim0 i
  | succ n =>
      let π : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
      have he : MeasurePreserving e (μ.prod π) (Measure.pi (fun _ : Fin (n+1) => μ)) :=
        (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => μ) i).symm
      let F : ℝ × (Fin n → ℝ) → ℝ := fun z => f (e z)
      have hF : Measurable F := hf.comp e.measurable
      have hFb (z : ℝ × (Fin n → ℝ)) : ‖F z‖ ≤ C := hb _
      have hFi : Integrable F (μ.prod π) := vt_integrable _ hF C hFb
      have hupdate (z : ℝ × (Fin n → ℝ)) (t : ℝ) :
          Function.update (e z) i t = e (t,z.2) := by
        simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Equiv.coe_fn_mk, Fin.update_insertNth]
      rw [← he.integral_comp' (fun x => ∫ t, f (Function.update x i t) ∂μ),
        ← he.integral_comp' f]
      simp_rw [hupdate]
      change (∫ z, ∫ t, F (t,z.2) ∂μ ∂μ.prod π) = ∫ z, F z ∂μ.prod π
      have hGm : Measurable (fun z : ℝ × (Fin n → ℝ) => ∫ t, F (t,z.2) ∂μ) :=
        hF.stronglyMeasurable.integral_prod_left'.measurable.comp measurable_snd
      have hGb (z : ℝ × (Fin n → ℝ)) : ‖∫ t, F (t,z.2) ∂μ‖ ≤ C :=
        vt_integral_bound μ C (fun t => hFb (t,z.2))
      rw [integral_prod _ (vt_integrable _ hGm C hGb), integral_prod_symm _ hFi]
      simp

/-- Gaussian form of the coordinate-resampling identity for bounded measurable
functions, used for the squared partial derivatives of the hinge objective. -/
theorem gaussian_integral_coordinate_resampling (d : ℕ) (f : (Fin d → ℝ) → ℝ)
    (hf : Measurable f) (hbounded : ∃ C : ℝ, ∀ x, |f x| ≤ C) (i : Fin d) :
    (∫ x, ∫ t, f (Function.update x i t) ∂gaussianReal 0 1
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
        ∫ x, f x ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
  obtain ⟨C, hC⟩ := hbounded
  exact bounded_integral_coordinate_resampling (gaussianReal 0 1) d f hf C
    (by simpa only [Real.norm_eq_abs] using hC) i

end NLA.IE22
