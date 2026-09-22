import NLA.IE22.GaussianPoincare
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
Actual hinge regularity for the scalar Gaussian variance foundation.
Original application: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology
namespace NLA.IE22

/-- Cauchy--Schwarz against the constant function, proved by integrating a square. -/
theorem integral_square_le_mass (μ : Measure ℝ) [IsFiniteMeasure μ]
    (D : ℝ → ℝ) (hD : MemLp D 2 μ) (hmass : 0 < μ.real univ) :
    (∫ s, D s ∂μ) ^ 2 ≤ μ.real univ * ∫ s, D s ^ 2 ∂μ := by
  let c := (∫ s, D s ∂μ) / μ.real univ
  have hi := hD.integrable (by norm_num)
  have hi2 := hD.integrable_sq
  have hs : (∫ s, (D s - c) ^ 2 ∂μ) =
      (∫ s, D s ^ 2 ∂μ) - 2 * c * (∫ s, D s ∂μ) + c ^ 2 * μ.real univ := by
    simp_rw [sub_sq]
    have hlin : Integrable (fun s => 2 * D s * c) μ := (hi.const_mul 2).mul_const c
    have hleft : Integrable (fun s => D s ^ 2 - 2 * D s * c) μ := hi2.sub hlin
    rw [integral_add hleft (integrable_const _), integral_sub hi2 hlin,
      integral_mul_const, integral_const_mul]
    simp only [integral_const, smul_eq_mul]
    ring
  have hn : 0 ≤ (∫ s, D s ^ 2 ∂μ) - 2 * c * (∫ s, D s ∂μ) + c ^ 2 * μ.real univ := by
    rw [← hs]
    exact integral_nonneg (fun _ => sq_nonneg _)
  have halg : μ.real univ *
      ((∫ s, D s ^ 2 ∂μ) - 2 * c * (∫ s, D s ∂μ) + c ^ 2 * μ.real univ) =
      μ.real univ * (∫ s, D s ^ 2 ∂μ) - (∫ s, D s ∂μ) ^ 2 := by
    dsimp [c]
    field_simp
    ring
  have h := mul_nonneg hmass.le hn
  rw [halg] at h
  linarith

/-- A bounded measurable representative of the almost-everywhere derivative of
an absolutely continuous function satisfies the required interval energy. -/
theorem interval_energy_of_absolutelyContinuous (f D : ℝ → ℝ)
    (hD : Measurable D) (C : ℝ) (hbound : ∀ s, ‖D s‖ ≤ C)
    (hderiv : ∀ᵐ s, HasDerivAt f (D s) s)
    (hac : ∀ x y : ℝ, AbsolutelyContinuousOnInterval f x y) :
    ∀ x y : ℝ, x ≤ y →
      IntegrableOn (fun s => D s ^ 2) (Ico x y) ∧
      (f y - f x) ^ 2 ≤ (y - x) * ∫ s in Ico x y, D s ^ 2 := by
  intro x y hxy
  have hLp : MemLp D 2 (volume.restrict (Ico x y)) :=
    MemLp.of_bound hD.aestronglyMeasurable C (ae_of_all _ hbound)
  refine ⟨hLp.integrable_sq, ?_⟩
  obtain rfl | hlt := hxy.eq_or_lt
  · simp
  have hFTC : (∫ s in Ico x y, D s) = f y - f x := by
    rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hxy,
      ← (hac x y).integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with s hs
    intro _
    exact hs.deriv.symm
  rw [← hFTC]
  have hm : (volume.restrict (Ico x y)).real univ = y - x := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ico_of_le hxy]
  simpa only [hm] using integral_square_le_mass (volume.restrict (Ico x y)) D hLp
    (by rw [hm]; linarith)

/-- An affine row's actual hinge, including zero row coefficients. -/
def affineHinge (t a b s : ℝ) : ℝ := max (t - (a * s + b) ^ 2) 0

/-- A measurable derivative representative; values at the breakpoints are zero. -/
def affineHingeDerivative (t a b s : ℝ) : ℝ :=
  if (a * s + b) ^ 2 < t then -2 * a * (a * s + b) else 0

@[fun_prop]
theorem affineHinge_continuous (t a b : ℝ) : Continuous (affineHinge t a b) := by
  unfold affineHinge
  fun_prop

@[fun_prop]
theorem affineHingeDerivative_measurable (t a b : ℝ) :
    Measurable (affineHingeDerivative t a b) := by
  unfold affineHingeDerivative
  exact Measurable.ite (by measurability) (by fun_prop) measurable_const

theorem affineHinge_absolutelyContinuous (t a b x y : ℝ) :
    AbsolutelyContinuousOnInterval (affineHinge t a b) x y := by
  have hc : ContDiff ℝ 1 (fun s : ℝ => t - (a * s + b) ^ 2) := by fun_prop
  have hl : LocallyLipschitz (affineHinge t a b) := hc.locallyLipschitz.max_const 0
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    isCompact_uIcc hl.locallyLipschitzOn
  exact hK.absolutelyContinuousOnInterval

theorem affineHinge_hasDerivAt_of_ne (t a b s : ℝ)
    (hne : (a * s + b) ^ 2 ≠ t) :
    HasDerivAt (affineHinge t a b) (affineHingeDerivative t a b s) s := by
  have hc : Continuous (fun u : ℝ => (a * u + b) ^ 2) := by fun_prop
  by_cases hlt : (a * s + b) ^ 2 < t
  · have hd : HasDerivAt (fun u : ℝ => t - (a * u + b) ^ 2)
        (-2 * a * (a * s + b)) s := by
      convert! (((hasDerivAt_id s).const_mul a).add_const b).pow 2 |>.const_sub t using 1
      simp only [id_eq]
      ring
    simp only [affineHingeDerivative, if_pos hlt]
    apply hd.congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.tendsto.eventually_lt_const hlt] with u hu
    exact max_eq_left (sub_nonneg.mpr hu.le)
  · have hgt : t < (a * s + b) ^ 2 := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    simp only [affineHingeDerivative, if_neg hlt]
    apply (hasDerivAt_const s (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [hc.continuousAt.tendsto.eventually_const_lt hgt] with u hu
    exact max_eq_right (sub_nonpos.mpr hu.le)

/-- The exceptional set consists of at most two real points for a nonconstant
row. Constant rows, including those exactly at the threshold, are handled directly. -/
theorem affineHinge_ae_hasDerivAt (t : ℝ) (ht : 0 ≤ t) (a b : ℝ) :
    ∀ᵐ s, HasDerivAt (affineHinge t a b) (affineHingeDerivative t a b s) s := by
  by_cases ha : a = 0
  · subst a
    exact ae_of_all _ (fun s => by
      unfold affineHinge affineHingeDerivative
      simpa using! hasDerivAt_const s (max (t - b ^ 2) 0))
  · filter_upwards [volume.ae_ne ((Real.sqrt t - b) / a),
      volume.ae_ne ((-Real.sqrt t - b) / a)] with s hp hn
    apply affineHinge_hasDerivAt_of_ne
    intro heq
    have hsq : (a * s + b) ^ 2 = (Real.sqrt t) ^ 2 := by rw [heq, Real.sq_sqrt ht]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · apply hp
      apply (eq_div_iff ha).2
      linarith
    · apply hn
      apply (eq_div_iff ha).2
      linarith

/-- A global bound for the actual derivative representative. -/
theorem affineHingeDerivative_bound (t : ℝ) (_ht : 0 ≤ t) (a b s : ℝ) :
    ‖affineHingeDerivative t a b s‖ ≤ 2 * |a| * Real.sqrt t := by
  unfold affineHingeDerivative
  split_ifs with h
  · have hu : |a * s + b| ≤ Real.sqrt t := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt h.le
    simp only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
  · simp only [norm_zero]
    positivity

/-- Constant plus a finite linear combination of row hinges. -/
def affineHingeSum {m : ℕ} (c q t : ℝ) (a b : Fin m → ℝ) (s : ℝ) : ℝ :=
  c - q * ∑ i, affineHinge t (a i) (b i) s

def affineHingeSumDerivative {m : ℕ} (q t : ℝ) (a b : Fin m → ℝ) (s : ℝ) : ℝ :=
  -q * ∑ i, affineHingeDerivative t (a i) (b i) s

@[fun_prop]
theorem affineHingeSum_continuous {m : ℕ} (c q t : ℝ) (a b : Fin m → ℝ) :
    Continuous (affineHingeSum c q t a b) := by
  unfold affineHingeSum
  fun_prop

@[fun_prop]
theorem affineHingeSumDerivative_measurable {m : ℕ} (q t : ℝ) (a b : Fin m → ℝ) :
    Measurable (affineHingeSumDerivative q t a b) := by
  unfold affineHingeSumDerivative
  fun_prop

theorem affineHinge_norm_le (t : ℝ) (ht : 0 ≤ t) (a b s : ℝ) :
    ‖affineHinge t a b s‖ ≤ t := by
  rw [affineHinge, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (sub_le_self _ (sq_nonneg _)) ht

theorem affineHingeSum_norm_le {m : ℕ} (c q t : ℝ) (ht : 0 ≤ t) (a b : Fin m → ℝ)
    (s : ℝ) : ‖affineHingeSum c q t a b s‖ ≤ |c| + |q| * ((m : ℝ) * t) := by
  calc
    _ ≤ ‖c‖ + ‖q * ∑ i, affineHinge t (a i) (b i) s‖ := norm_sub_le _ _
    _ = |c| + |q| * ‖∑ i, affineHinge t (a i) (b i) s‖ := by rw [norm_mul]; rfl
    _ ≤ |c| + |q| * ∑ i, ‖affineHinge t (a i) (b i) s‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ |c| + |q| * ∑ _ : Fin m, t := by
      gcongr with i
      exact affineHinge_norm_le t ht (a i) (b i) s
    _ = _ := by simp

theorem affineHingeSum_memLp {m : ℕ} (c q t : ℝ) (ht : 0 ≤ t) (a b : Fin m → ℝ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (affineHingeSum c q t a b) p μ :=
  MemLp.of_bound (affineHingeSum_continuous c q t a b).aestronglyMeasurable
    (|c| + |q| * ((m : ℝ) * t)) (ae_of_all _ (affineHingeSum_norm_le c q t ht a b))

theorem affineHingeSumDerivative_bound {m : ℕ} (q t : ℝ) (ht : 0 ≤ t)
    (a b : Fin m → ℝ) (s : ℝ) :
    ‖affineHingeSumDerivative q t a b s‖ ≤ |q| * ∑ i, 2 * |a i| * Real.sqrt t := by
  rw [affineHingeSumDerivative, norm_mul, norm_neg, Real.norm_eq_abs]
  calc
    _ ≤ |q| * ∑ i, ‖affineHingeDerivative t (a i) (b i) s‖ := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ _ := by
      gcongr with i
      exact affineHingeDerivative_bound t ht (a i) (b i) s

theorem affineHingeSum_absolutelyContinuous {m : ℕ} (c q t : ℝ) (a b : Fin m → ℝ)
    (x y : ℝ) : AbsolutelyContinuousOnInterval (affineHingeSum c q t a b) x y := by
  have hsum (S : Finset (Fin m)) :
      AbsolutelyContinuousOnInterval (fun s => ∑ i ∈ S, affineHinge t (a i) (b i) s) x y := by
    induction S using Finset.induction_on with
    | empty =>
      simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
    | @insert i S hi ih =>
      simpa only [Finset.sum_insert hi] using
        (affineHinge_absolutelyContinuous t (a i) (b i) x y).fun_add ih
  exact (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval.fun_sub
    ((hsum Finset.univ).const_mul q)

theorem affineHingeSum_ae_hasDerivAt {m : ℕ} (c q t : ℝ) (ht : 0 ≤ t) (a b : Fin m → ℝ) :
    ∀ᵐ s, HasDerivAt (affineHingeSum c q t a b) (affineHingeSumDerivative q t a b s) s := by
  have hrows : ∀ᵐ s, ∀ i : Fin m,
      HasDerivAt (affineHinge t (a i) (b i)) (affineHingeDerivative t (a i) (b i) s) s :=
    ae_all_iff.mpr (fun i => affineHinge_ae_hasDerivAt t ht (a i) (b i))
  filter_upwards [hrows] with s hs
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hs i)
  have h := (hsum.const_mul q).const_sub c
  simpa only [affineHingeSum, affineHingeSumDerivative, neg_mul] using! h

theorem affineHingeSum_gaussian_variance {m : ℕ} (c q t : ℝ) (ht : 0 ≤ t)
    (a b : Fin m → ℝ) :
    Var[affineHingeSum c q t a b; gaussianReal 0 1] ≤
      ∫ s, affineHingeSumDerivative q t a b s ^ 2 ∂gaussianReal 0 1 := by
  have hD := affineHingeSumDerivative_measurable q t a b
  have hbound := affineHingeSumDerivative_bound q t ht a b
  have hLp : MemLp (affineHingeSumDerivative q t a b) 2 (gaussianReal 0 1) :=
    MemLp.of_bound hD.aestronglyMeasurable _ (ae_of_all _ hbound)
  apply gaussian_poincare_of_interval_energy _ _
    (affineHingeSum_memLp c q t ht a b _ 2) hD hLp.integrable_sq
  exact interval_energy_of_absolutelyContinuous _ _ hD _ hbound
    (affineHingeSum_ae_hasDerivAt c q t ht a b)
    (affineHingeSum_absolutelyContinuous c q t a b)

end NLA.IE22

