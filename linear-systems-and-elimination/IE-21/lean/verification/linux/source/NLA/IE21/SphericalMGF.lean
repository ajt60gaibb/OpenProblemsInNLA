import NLA.IE21.SphericalMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
The exact quadratic MGF bound for IE-21, including the centered first-order cancellation.
Original proof: Matthew J. Colbrook. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of Technology.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace

namespace NLA.IE21

theorem centered_directionalEnergy_abs_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) :
    ∀ᵐ u ∂sphereLaw n, |directionalEnergy x u - 1| ≤ (n : ℝ) + 1 := by
  filter_upwards [sphere_norm_ae n hn] with u hu
  have h := directionalEnergy_bounds x u hx hu
  rw [abs_le]
  constructor <;> linarith

theorem centered_directionalEnergy_pow_integrable (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    Integrable (fun u => |directionalEnergy x u - 1| ^ r) (sphereLaw n) := by
  let := (surface_probability n hn).2.2.2.1
  apply (integrable_const (((n : ℝ) + 1) ^ r)).mono'
    (by unfold directionalEnergy; fun_prop)
  filter_upwards [centered_directionalEnergy_abs_bound n hn x hx] with u hu
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  exact pow_le_pow_left₀ (abs_nonneg _) hu r

theorem centered_directionalEnergy_moment_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, |directionalEnergy x u - 1| ^ r ∂sphereLaw n) ≤
      4 ^ r * (Nat.factorial r : ℝ) := by
  let := (surface_probability n hn).2.2.2.1
  cases r with
  | zero => simp
  | succ r =>
      have hpoint : ∀ᵐ u ∂sphereLaw n,
          |directionalEnergy x u - 1| ^ (r + 1) ≤
            2 ^ r * (directionalEnergy x u ^ (r + 1) + 1) := by
        filter_upwards [sphere_norm_ae n hn] with u hu
        have hy := (directionalEnergy_bounds x u hx hu).1
        have habs : |directionalEnergy x u - 1| ≤ directionalEnergy x u + 1 := by
          rw [abs_le]
          constructor <;> linarith
        calc
          _ ≤ (directionalEnergy x u + 1) ^ (r + 1) :=
            pow_le_pow_left₀ (abs_nonneg _) habs _
          _ ≤ _ := by simpa only [Nat.add_sub_cancel, one_pow] using
            add_pow_le hy (by norm_num : (0 : ℝ) ≤ 1) (r + 1)
      have hi := integral_mono_ae (centered_directionalEnergy_pow_integrable n hn x hx (r + 1))
        (((directionalEnergy_pow_integrable n hn x hx (r + 1)).add (integrable_const 1)).const_mul
          (2 ^ r)) hpoint
      rw [integral_const_mul] at hi
      simp only [Pi.add_apply] at hi
      rw [integral_add (directionalEnergy_pow_integrable n hn x hx (r + 1)) (integrable_const 1)] at hi
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
      have hmoment := spherical_moment_bound n hn x hx (r + 1)
      have hfact : (1 : ℝ) ≤ (Nat.factorial (r + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (r + 1)
      have hpow : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
      have hone : (1 : ℝ) ≤ 2 ^ (r + 1) * (Nat.factorial (r + 1) : ℝ) :=
        one_le_mul_of_one_le_of_one_le hpow hfact
      calc
        _ ≤ 2 ^ r * ((2 ^ (r + 1) * (Nat.factorial (r + 1) : ℝ)) + 1) :=
          hi.trans (mul_le_mul_of_nonneg_left (by linarith [hmoment]) (by positivity))
        _ ≤ 2 ^ r * (2 * (2 ^ (r + 1) * (Nat.factorial (r + 1) : ℝ))) := by
          gcongr
          linarith
        _ = _ := by
          rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, pow_succ]
          ring

theorem real_exp_hasSum (t : ℝ) :
    HasSum (fun r : ℕ => t ^ r / (Nat.factorial r : ℝ)) (Real.exp t) := by
  simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp t

theorem integral_exp_series_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → ℝ) (hZ : Measurable Z)
    (B : ℝ) (_hB : 0 ≤ B) (hbound : ∀ᵐ u ∂μ, |Z u| ≤ B) (a : ℝ) :
    HasSum (fun r : ℕ => ∫ u, (a * Z u) ^ r / (Nat.factorial r : ℝ) ∂μ)
      (∫ u, Real.exp (a * Z u) ∂μ) := by
  let C := |a| * B
  apply hasSum_integral_of_dominated_convergence (fun r _ => C ^ r / (Nat.factorial r : ℝ))
  · intro r
    fun_prop
  · intro r
    filter_upwards [hbound] with u hu
    simp only [norm_div, norm_pow, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  · exact Filter.Eventually.of_forall (fun _ => (real_exp_hasSum C).summable)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun u => real_exp_hasSum (a * Z u))

theorem centered_exp_term_norm_integral (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (a : ℝ) (r : ℕ) :
    ‖∫ u, (a * (directionalEnergy x u - 1)) ^ r / (Nat.factorial r : ℝ) ∂sphereLaw n‖ ≤
      (4 * |a|) ^ r := by
  have hfact : (Nat.factorial r : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hnorm (u : Space n) :
      ‖(a * (directionalEnergy x u - 1)) ^ r / (Nat.factorial r : ℝ)‖ =
        (|a| ^ r / (Nat.factorial r : ℝ)) * |directionalEnergy x u - 1| ^ r := by
    simp only [norm_div, Real.norm_eq_abs, abs_mul, Nat.abs_cast, mul_pow, abs_pow]
    ring
  calc
    _ ≤ ∫ u, ‖(a * (directionalEnergy x u - 1)) ^ r / (Nat.factorial r : ℝ)‖
        ∂sphereLaw n := norm_integral_le_integral_norm _
    _ = (|a| ^ r / (Nat.factorial r : ℝ)) *
        (∫ u, |directionalEnergy x u - 1| ^ r ∂sphereLaw n) := by
      simp_rw [hnorm]
      rw [integral_const_mul]
    _ ≤ (|a| ^ r / (Nat.factorial r : ℝ)) * (4 ^ r * (Nat.factorial r : ℝ)) :=
      mul_le_mul_of_nonneg_left (centered_directionalEnergy_moment_bound n hn x hx r)
        (by positivity)
    _ = (4 * |a|) ^ r := by rw [mul_pow]; field_simp

theorem spherical_quadratic_mgf (n : ℕ) (hn : 2 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (a : ℝ) (ha : |a| ≤ 1 / 8) :
    Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) ∧
    (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) ≤
      Real.exp (32 * a ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  let := (surface_probability n hn1).2.2.2.1
  have hbound := centered_directionalEnergy_abs_bound n hn1 x hx
  have hexp : Integrable (fun u => Real.exp (a * (directionalEnergy x u - 1))) (sphereLaw n) := by
    apply (integrable_const (Real.exp (|a| * ((n : ℝ) + 1)))).mono'
      (by unfold directionalEnergy; fun_prop)
    filter_upwards [hbound] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |a * (directionalEnergy x u - 1)| := le_abs_self _
      _ = |a| * |directionalEnergy x u - 1| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  refine ⟨hexp, ?_⟩
  let I : ℕ → ℝ := fun r => ∫ u,
    (a * (directionalEnergy x u - 1)) ^ r / (Nat.factorial r : ℝ) ∂sphereLaw n
  have hseries : HasSum I (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) :=
    integral_exp_series_of_bounded (sphereLaw n) (fun u => directionalEnergy x u - 1)
      (by unfold directionalEnergy; fun_prop) ((n : ℝ) + 1) (by positivity) hbound a
  have hzero : I 0 = 1 := by simp [I]
  have hone : I 1 = 0 := by
    simp only [I, pow_one, Nat.factorial_one, Nat.cast_one, div_one]
    rw [integral_const_mul, integral_sub (directionalEnergy_integrable n hn1 x hx) (integrable_const 1),
      directionalEnergy_mean n hn1 x hx]
    simp
  have htwo : ∑ r ∈ Finset.range 2, I r = 1 := by simp [Finset.sum_range_succ, hzero, hone]
  have htail := (hasSum_nat_add_iff' 2).2 hseries
  rw [htwo] at htail
  let q : ℝ := 4 * |a|
  have hq0 : 0 ≤ q := by positivity
  have hqhalf : q ≤ 1 / 2 := by dsimp [q]; linarith [ha]
  have hq1 : q < 1 := by linarith
  have hgeo : HasSum (fun r : ℕ => q ^ (r + 2)) (q ^ 2 / (1 - q)) := by
    have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_right (q ^ 2)
    simpa only [pow_add, div_eq_mul_inv, mul_comm] using h
  have htaille : (∫ u, Real.exp (a * (directionalEnergy x u - 1)) ∂sphereLaw n) - 1 ≤
      q ^ 2 / (1 - q) := by
    apply le_of_tendsto_of_tendsto htail.tendsto_sum_nat hgeo.tendsto_sum_nat
    exact Filter.Eventually.of_forall (fun N => Finset.sum_le_sum (fun r _ =>
      (le_abs_self (I (r + 2))).trans
        (centered_exp_term_norm_integral n hn1 x hx a (r + 2))))
  have htailbound : q ^ 2 / (1 - q) ≤ 32 * a ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - q)).2
    have hq2 : q ^ 2 = 16 * a ^ 2 := by dsimp [q]; rw [mul_pow, sq_abs]; ring
    rw [hq2]
    nlinarith [sq_nonneg a]
  have hfinal := htaille.trans htailbound
  have hexple := Real.add_one_le_exp (32 * a ^ 2)
  linarith

end NLA.IE21
