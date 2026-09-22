import NLA.IE21.GaussianMoments
import Mathlib.Probability.Independence.Integration

/-!
Exact all-orders directional moments of normalized Euclidean surface measure.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace NLA.IE21

theorem gaussian_real_even_moment (r : ℕ) :
    (∫ t : ℝ, t ^ (2 * r) ∂gaussianReal 0 1) =
      ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1) := by
  let e : Space 1 := EuclideanSpace.single 0 1
  have he : ‖e‖ = 1 := by simp [e]
  rw [← gaussian_projection_law e he,
    integral_map (by fun_prop) (by fun_prop)]
  have hnorm (g : Space 1) : (inner ℝ e g) ^ (2 * r) = ‖g‖ ^ (2 * r) := by
    rw [pow_mul, pow_mul]
    congr 1
    simp [e, EuclideanSpace.inner_single_left, EuclideanSpace.real_norm_sq_eq]
  simp_rw [hnorm]
  simpa only [Nat.cast_one, add_comm] using gaussian_norm_even_moment 1 (by omega) r

theorem sphere_norm_ae (n : ℕ) (hn : 1 ≤ n) : ∀ᵐ u ∂sphereLaw n, ‖u‖ = 1 := by
  let := (surface_probability n hn).2.2.2.1
  exact (ae_iff_prob_eq_one (by fun_prop)).2 (surface_probability n hn).2.2.2.2

theorem directionalEnergy_bounds {n : ℕ} (x u : Space n) (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    0 ≤ directionalEnergy x u ∧ directionalEnergy x u ≤ n := by
  have habs : |inner ℝ u x| ≤ 1 := by
    simpa only [hx, hu, one_mul] using abs_real_inner_le_norm u x
  have hs : (inner ℝ u x) ^ 2 ≤ 1 := by nlinarith [abs_le.mp habs]
  unfold directionalEnergy
  constructor
  · positivity
  · nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem directionalEnergy_pow_integrable (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    Integrable (fun u => directionalEnergy x u ^ r) (sphereLaw n) := by
  let := (surface_probability n hn).2.2.2.1
  apply (integrable_const ((n : ℝ) ^ r)).mono' (by unfold directionalEnergy; fun_prop)
  filter_upwards [sphere_norm_ae n hn] with u hu
  have h := directionalEnergy_bounds x u hx hu
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h.1 _)]
  exact pow_le_pow_left₀ h.1 h.2 r

theorem norm_smul_gaussianDirection {n : ℕ} (g : Space n) : ‖g‖ • gaussianDirection g = g := by
  by_cases hg : g = 0
  · simp [hg, gaussianDirection]
  · rw [gaussianDirection, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hg), one_smul]

theorem gaussian_inner_even_moment {n : ℕ} (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ g : Space n, (inner ℝ g x) ^ (2 * r) ∂stdGaussian (Space n)) =
      ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1) := by
  rw [← gaussian_real_even_moment r, ← gaussian_projection_law x hx,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [real_inner_comm]

theorem spherical_inner_factorization (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) *
      (∫ u, (inner ℝ u x) ^ (2 * r) ∂sphereLaw n) =
      ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1) := by
  have hfac := (gaussian_radius_direction_independent n hn).integral_fun_comp_mul_comp
    (f := fun t : ℝ => t ^ (2 * r))
    (g := fun u : Space n => (inner ℝ u x) ^ (2 * r))
    measurable_norm.aemeasurable (measurable_gaussianDirection n).aemeasurable
    (by fun_prop) (by fun_prop)
  have hpoint (g : Space n) : ‖g‖ ^ (2 * r) *
      (inner ℝ (gaussianDirection g) x) ^ (2 * r) = (inner ℝ g x) ^ (2 * r) := by
    rw [← mul_pow]
    congr 1
    rw [← real_inner_smul_left, norm_smul_gaussianDirection]
  simp only [hpoint, gaussian_norm_even_moment n hn r, gaussian_inner_even_moment x hx r] at hfac
  have hmap : (∫ g : Space n, (inner ℝ (gaussianDirection g) x) ^ (2 * r)
      ∂stdGaussian (Space n)) = ∫ u, (inner ℝ u x) ^ (2 * r) ∂sphereLaw n := by
    rw [← gaussian_direction_law n hn,
      integral_map (measurable_gaussianDirection n).aemeasurable (by fun_prop)]
  rw [hmap] at hfac
  exact hfac.symm

theorem spherical_moment_formula (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) =
      ((n : ℝ) ^ r * ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) /
        (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hden : (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) ≠ 0 := by
    apply ne_of_gt
    exact Finset.prod_pos (fun j _ => by positivity)
  have h := spherical_inner_factorization n hn x hx r
  have hquot : (∫ u, (inner ℝ u x) ^ (2 * r) ∂sphereLaw n) =
      (∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) /
        (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) := by
    apply (eq_div_iff hden).2
    simpa only [mul_comm] using h
  simp only [directionalEnergy, mul_pow, ← pow_mul]
  rw [integral_const_mul, hquot, mul_div_assoc]

theorem directionalEnergy_integrable (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) : Integrable (directionalEnergy x) (sphereLaw n) := by
  simpa only [pow_one] using directionalEnergy_pow_integrable n hn x hx 1

theorem directionalEnergy_mean (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) :
    (∫ u, directionalEnergy x u ∂sphereLaw n) = 1 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simpa [hnR] using spherical_moment_formula n hn x hx 1

theorem odd_product_le_factorial (r : ℕ) :
    (∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) ≤ 2 ^ r * (Nat.factorial r : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.prod_range_succ]
      calc
        _ ≤ (2 ^ r * (Nat.factorial r : ℝ)) * (2 * (r + 1)) := by
          apply mul_le_mul ih (by linarith)
          · positivity
          · positivity
        _ = 2 ^ (r + 1) * (Nat.factorial (r + 1) : ℝ) := by
          rw [pow_succ, Nat.factorial_succ]
          push_cast
          ring

theorem spherical_moment_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) ≤ 2 ^ r * (Nat.factorial r : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hd : 0 < ∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j) :=
    Finset.prod_pos (fun j _ => by positivity)
  have hden : (n : ℝ) ^ r ≤ ∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j) := by
    have h := Finset.prod_le_prod (s := Finset.range r)
      (f := fun _ : ℕ => (n : ℝ)) (g := fun j : ℕ => (n : ℝ) + 2 * (j : ℝ))
      (fun _ _ => hnR.le) (fun j _ => le_add_of_nonneg_right (by positivity))
    simpa only [Finset.prod_const, Finset.card_range] using h
  rw [spherical_moment_formula n hn x hx r]
  apply (div_le_iff₀ hd).2
  calc
    _ ≤ (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) *
        (2 ^ r * (Nat.factorial r : ℝ)) :=
      mul_le_mul hden (odd_product_le_factorial r)
        (Finset.prod_nonneg (fun j _ => by positivity)) hd.le
    _ = _ := by ring

theorem spherical_moments (n : ℕ) (hn : 2 ≤ n) (x : Space n) (hx : ‖x‖ = 1)
    (r : ℕ) :
    Integrable (fun u => directionalEnergy x u ^ r) (sphereLaw n) ∧
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) =
      ((n : ℝ) ^ r * ∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) /
        (∏ j ∈ Finset.range r, ((n : ℝ) + 2 * j)) ∧
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) ≤
      2 ^ r * (Nat.factorial r : ℝ) :=
  ⟨directionalEnergy_pow_integrable n (by omega) x hx r,
    spherical_moment_formula n (by omega) x hx r,
    spherical_moment_bound n (by omega) x hx r⟩

end NLA.IE21
