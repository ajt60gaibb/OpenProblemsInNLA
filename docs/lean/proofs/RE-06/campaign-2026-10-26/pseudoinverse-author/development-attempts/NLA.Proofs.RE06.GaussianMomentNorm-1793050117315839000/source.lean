import NLA.Proofs.RE06.GaussianMomentLaplace

/-! The actual finite-product Gaussian reciprocal squared-norm moment, proved
by nonnegative Laplace inversion and Tonelli. No chi-square law is assumed. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Set
open scoped BigOperators ENNReal

namespace NLA.Proofs.RE06.GaussianMoment

def normSq {d : ℕ} (x : Fin d → ℝ) : ℝ := ∑ i, (x i) ^ 2

theorem normSq_nonneg {d : ℕ} (x : Fin d → ℝ) : 0 ≤ normSq x :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (x i))

theorem normSq_pos_ae (d : ℕ) (hd : 0 < d) :
    ∀ᵐ x : Fin d → ℝ ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1), 0 < normSq x := by
  let i : Fin d := ⟨0, hd⟩
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal (by norm_num)
  have hn := Measure.ae_eval_ne (fun _ : Fin d => gaussianReal 0 1) i (0 : ℝ)
  filter_upwards [hn] with x hx
  have hs : 0 < (x i) ^ 2 := sq_pos_of_ne_zero hx
  have hl : (x i) ^ 2 ≤ normSq x :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  exact hs.trans_le hl

theorem normSq_laplace (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ x : Fin d → ℝ, Real.exp (-t * normSq x)
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
      (2 * t + 1) ^ (-(d : ℝ) / 2) := by
  have hh := gaussianQuadratic_exp_integral_log (fun _ : Fin d => (1 : ℝ)) (-t)
    (by intro i; linarith)
  have hbase : 0 < 2 * t + 1 := by linarith
  calc
    _ = Real.exp (-((d : ℝ) * Real.log (1 - 2 * (-t))) / 2) := by
      simpa [gaussianQuadratic, normSq] using hh
    _ = (2 * t + 1) ^ (-(d : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hbase]
      congr 1
      have hb : 1 - 2 * (-t) = 2 * t + 1 := by ring
      rw [hb]
      ring

theorem normSq_laplace_integrable (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (fun x : Fin d → ℝ => Real.exp (-t * normSq x))
      (Measure.pi (fun _ : Fin d => gaussianReal 0 1)) := by
  by_contra h
  have he := normSq_laplace d t ht
  rw [integral_undef h] at he
  exact (Real.rpow_pos_of_pos (by linarith : 0 < 2 * t + 1) _).ne he

theorem normSq_laplace_lintegral (d : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (Real.exp (-t * normSq x))
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
      ENNReal.ofReal ((2 * t + 1) ^ (-(d : ℝ) / 2)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (normSq_laplace_integrable d t ht)
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le)), normSq_laplace d t ht]

theorem normSq_inverse_lintegral (d : ℕ) (hd : 2 < d) :
    (∫⁻ x : Fin d → ℝ, ENNReal.ofReal (normSq x)⁻¹
      ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1)) =
      ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
  have hdp : 0 < d := by omega
  have hpr : -(d : ℝ) / 2 < -1 := by
    have hdr : (2 : ℝ) < d := by exact_mod_cast hd
    linarith
  calc
    _ = ∫⁻ x : Fin d → ℝ, (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-normSq x * t)))
        ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
      apply lintegral_congr_ae
      filter_upwards [normSq_pos_ae d hdp] with x hx
      exact (scalar_inverse_laplace (normSq x) hx).symm
    _ = ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x : Fin d → ℝ,
        ENNReal.ofReal (Real.exp (-normSq x * t))
          ∂Measure.pi (fun _ : Fin d => gaussianReal 0 1) := by
      apply lintegral_lintegral_swap
      apply Measurable.ennreal_ofReal
      apply Continuous.measurable
      unfold normSq
      fun_prop
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((2 * t + 1) ^ (-(d : ℝ) / 2)) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have heq : (fun x : Fin d → ℝ => ENNReal.ofReal (Real.exp (-normSq x * t))) =
          (fun x => ENNReal.ofReal (Real.exp (-t * normSq x))) := by
        funext x
        congr 2
        ring
      rw [heq]
      exact normSq_laplace_lintegral d t (le_of_lt ht)
    _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, (2 * t + 1) ^ (-(d : ℝ) / 2)) := by
      exact (ofReal_integral_eq_lintegral_ofReal (affine_power_integrable _ hpr)
        (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.rpow_nonneg (by linarith [mem_Ioi.mp ht]) _)).symm
    _ = ENNReal.ofReal (1 / ((d : ℝ) - 2)) := by
      rw [affine_power_integral _ hpr]
      congr 1
      have he : 2 * (-(d : ℝ) / 2 + 1) = -((d : ℝ) - 2) := by ring
      rw [he, div_neg, neg_neg]

#assert_trust kernel normSq_inverse_lintegral
#print axioms normSq_inverse_lintegral
end NLA.Proofs.RE06.GaussianMoment
