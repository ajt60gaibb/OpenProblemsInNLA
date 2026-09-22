import NLA.IE21.GaussianPolar
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
Exact Gaussian radius moments, using a single radial Gamma-integral recurrence.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace NLA.IE21

def radialIntegral (k : ℝ) : ℝ :=
  ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-(r ^ 2) / 2)

theorem radialIntegral_gamma {k : ℝ} (hk : 0 < k) :
    radialIntegral k = (1 / 2 : ℝ) ^ (-k / 2) * (1 / 2) * Real.Gamma (k / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := k - 1) (b := 1 / 2) (by norm_num) (by linarith) (by norm_num)
  have hexp (r : ℝ) : -(1 / 2 : ℝ) * r ^ 2 = -(r ^ 2) / 2 := by ring
  simpa only [radialIntegral, Real.rpow_two, hexp, sub_add_cancel] using h

theorem radialIntegral_add_two {k : ℝ} (hk : 0 < k) :
    radialIntegral (k + 2) = k * radialIntegral k := by
  rw [radialIntegral_gamma (by linarith), radialIntegral_gamma hk]
  have he : -(k + 2) / 2 = -k / 2 + (-1) := by ring
  have he' : (k + 2) / 2 = k / 2 + 1 := by ring
  rw [he, he', Real.rpow_add (by norm_num), Real.rpow_neg_one,
    Real.Gamma_add_one (by positivity)]
  ring

theorem gaussian_norm_pow_integrable (n r : ℕ) :
    Integrable (fun g : Space n => ‖g‖ ^ r) (stdGaussian (Space n)) := by
  simpa only [id_eq] using
    (IsGaussian.memLp_id (stdGaussian (Space n)) (r : ℝ≥0∞) (by simp)).integrable_norm_pow'

theorem gaussian_norm_even_integral (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (∫ g : Space n, ‖g‖ ^ (2 * r) ∂stdGaussian (Space n)) =
      ((n : ℝ) * (volume : Measure (Space n)).real (Metric.ball 0 1) *
        (Real.sqrt (2 * Real.pi))⁻¹ ^ n) * radialIntegral ((n : ℝ) + 2 * r) := by
  let : NeZero n := ⟨by omega⟩
  rw [stdGaussian_radial_density,
    integral_withDensity_eq_integral_toReal_smul
      (f := fun g : Space n => gaussianRadialDensity n ‖g‖)
      (by unfold gaussianRadialDensity; fun_prop)
      (Filter.Eventually.of_forall (fun g => ENNReal.ofReal_lt_top))]
  have hd (g : Space n) : (gaussianRadialDensity n ‖g‖).toReal =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-(‖g‖ ^ 2) / 2) := by
    unfold gaussianRadialDensity
    rw [ENNReal.toReal_ofReal (by positivity)]
  simp only [hd, smul_eq_mul]
  rw [integral_fun_norm_addHaar (volume : Measure (Space n))
    (fun y => (Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-(y ^ 2) / 2) * y ^ (2 * r))]
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  have hp : ∫ y in Ioi (0 : ℝ), y ^ (n - 1) *
      ((Real.sqrt (2 * Real.pi))⁻¹ ^ n * Real.exp (-(y ^ 2) / 2) * y ^ (2 * r)) =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ n * radialIntegral ((n : ℝ) + 2 * r) := by
    rw [radialIntegral, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    dsimp only
    have hn' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have hr' : ((2 * r : ℕ) : ℝ) = 2 * (r : ℝ) := by norm_cast
    rw [← Real.rpow_natCast y (n - 1), ← Real.rpow_natCast y (2 * r), hn', hr']
    have hexp : (n : ℝ) + 2 * r - 1 = ((n : ℝ) - 1) + 2 * r := by ring
    rw [hexp, Real.rpow_add hy]
    ring
  rw [hp]
  ring

theorem gaussian_norm_even_moment (n : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (∫ g : Space n, ‖g‖ ^ (2 * r) ∂stdGaussian (Space n)) =
      ∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ, ← ih,
        gaussian_norm_even_integral n hn (r + 1), gaussian_norm_even_integral n hn r]
      have ha : (n : ℝ) + 2 * (↑(r + 1) : ℝ) = ((n : ℝ) + 2 * r) + 2 := by
        push_cast
        ring
      rw [ha, radialIntegral_add_two (by positivity)]
      ring

theorem gaussian_norm_sq_mean (n : ℕ) (hn : 1 ≤ n) :
    (∫ g : Space n, ‖g‖ ^ 2 ∂stdGaussian (Space n)) = n := by
  simpa using gaussian_norm_even_moment n hn 1

theorem gaussian_norm_fourth_moment (n : ℕ) (hn : 1 ≤ n) :
    (∫ g : Space n, ‖g‖ ^ 4 ∂stdGaussian (Space n)) = (n : ℝ) * (n + 2) := by
  simpa [Finset.prod_range_succ] using gaussian_norm_even_moment n hn 2

theorem gaussian_norm_sq_centered_moment (n : ℕ) (hn : 1 ≤ n) :
    (∫ g : Space n, (‖g‖ ^ 2 - n) ^ 2 ∂stdGaussian (Space n)) = 2 * n := by
  have hp (g : Space n) : (‖g‖ ^ 2 - n) ^ 2 =
      ‖g‖ ^ 4 - (2 * n) * ‖g‖ ^ 2 + (n : ℝ) ^ 2 := by ring
  simp_rw [hp]
  rw [integral_add (f := fun g : Space n => ‖g‖ ^ 4 - (2 * n) * ‖g‖ ^ 2)
      (g := fun _ : Space n => (n : ℝ) ^ 2) ((gaussian_norm_pow_integrable n 4).sub
      ((gaussian_norm_pow_integrable n 2).const_mul (2 * n))) (integrable_const _),
    integral_sub (f := fun g : Space n => ‖g‖ ^ 4)
      (g := fun g : Space n => (2 * n) * ‖g‖ ^ 2) (gaussian_norm_pow_integrable n 4)
      ((gaussian_norm_pow_integrable n 2).const_mul (2 * n)),
    integral_const_mul, gaussian_norm_fourth_moment n hn, gaussian_norm_sq_mean n hn,
    integral_const]
  simp only [measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
  ring

theorem gaussian_surface_correspondence (n : ℕ) (hn : 1 ≤ n) :
    (stdGaussian (Space n)).map gaussianDirection = sphereLaw n ∧
    (stdGaussian (Space n)) {0} = 0 ∧
    IndepFun (fun g : Space n => ‖g‖) gaussianDirection (stdGaussian (Space n)) ∧
    (∫ g : Space n, ‖g‖ ^ 2 ∂stdGaussian (Space n)) = n ∧
    (∫ g : Space n, (‖g‖ ^ 2 - n) ^ 2 ∂stdGaussian (Space n)) = 2 * n :=
  ⟨gaussian_direction_law n hn, gaussian_zero_mass n hn,
    gaussian_radius_direction_independent n hn, gaussian_norm_sq_mean n hn,
    gaussian_norm_sq_centered_moment n hn⟩

end NLA.IE21
