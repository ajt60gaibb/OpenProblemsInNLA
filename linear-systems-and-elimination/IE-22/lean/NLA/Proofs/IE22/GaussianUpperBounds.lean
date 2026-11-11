import NLA.Proofs.IE22.GaussianTrimming
import NLA.Proofs.IE22.TrimmingDual

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace NLA.Proofs.IE22
open NLA.Statements.RowDeletion

/-- Contracting a scalar observation increases its lower trimming hinge. -/
theorem hinge_scale_mono {c : ℝ} (hc : c^2 ≤ 1) (t z : ℝ) :
    hinge t z ≤ hinge t (c*z) := by
  apply max_le_max _ le_rfl
  have h := mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg z)
  nlinarith

/-- Every genuine projected row of norm at most one has at least the standard
Gaussian hinge expectation, including a row of norm zero. -/
theorem gaussian_hinge_expectation_mono {n : ℕ} (b : Euclid n)
    (hb : ‖b‖^2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∫ z : ℝ, hinge t z ∂gaussianReal 0 1) ≤
      ∫ g : Euclid n, hinge t (inner ℝ b g) ∂stdGaussian (Euclid n) := by
  have hstd : Integrable (hinge t) (gaussianReal 0 1) :=
    (memLp_comp_lipschitz (memLp_id_gaussianReal' 2 (by norm_num))
      (hinge_lipschitz ht)).integrable (by norm_num)
  by_cases hb0 : b = 0
  · have h := integral_mono hstd (integrable_const t) (hinge_le ht)
    simpa [hb0, hinge, max_eq_left ht] using h
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  let v : Euclid n := ‖b‖⁻¹ • b
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
    exact inv_mul_cancel₀ hbpos.ne'
  have heq : b = ‖b‖ • v := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hbpos.ne', one_smul]
  have hlaw := gaussian_unit_inner_law v hv
  have hvInt : Integrable (fun g : Euclid n => hinge t (inner ℝ v g))
      (stdGaussian (Euclid n)) :=
    (memLp_comp_lipschitz (gaussian_inner_pair_law v v).fst.memLp_two
      (hinge_lipschitz ht)).integrable (by norm_num)
  have hbInt : Integrable (fun g : Euclid n => hinge t (inner ℝ b g))
      (stdGaussian (Euclid n)) :=
    (memLp_comp_lipschitz (gaussian_inner_pair_law b b).fst.memLp_two
      (hinge_lipschitz ht)).integrable (by norm_num)
  calc
    _ = ∫ g : Euclid n, hinge t (inner ℝ v g) ∂stdGaussian (Euclid n) := by
      rw [← hlaw, integral_map (by fun_prop) (hinge_lipschitz ht).continuous.aestronglyMeasurable]
    _ ≤ _ := by
      apply integral_mono hvInt hbInt
      intro g
      change hinge t (inner ℝ v g) ≤ hinge t (inner ℝ b g)
      have hi : inner ℝ b g = ‖b‖ * inner ℝ v g := by
        calc
          _ = inner ℝ (‖b‖ • v) g := congrArg (fun w => inner ℝ w g) heq
          _ = _ := by simp only [inner_smul_left, conj_trivial]
      rw [hi]
      exact hinge_scale_mono hb t (inner ℝ v g)

def gaussianTrimmingDual {m n : ℕ} (θ : ℝ) (b : Fin m → Euclid n) (t : ℝ)
    (g : Euclid n) : ℝ :=
  ((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ)*t -
    (1/(m : ℝ))*∑ i, hinge t (inner ℝ (b i) g)

/-- The expected finite trimming dual is bounded by the actual quantile moment. -/
theorem gaussianTrimmingDual_mean_le {m n : ℕ} (hm : 0 < m)
    {θ a : ℝ} (hθ0 : 0 ≤ θ) (ha : 0 ≤ a) (hq : GaussianQuantile θ a)
    (b : Fin m → Euclid n) (hb : ∀ i, ‖b i‖^2 ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    (∫ g : Euclid n, gaussianTrimmingDual θ b t g ∂stdGaussian (Euclid n)) ≤ TrimmedMoment a := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hInt (i : Fin m) : Integrable (fun g : Euclid n => hinge t (inner ℝ (b i) g))
      (stdGaussian (Euclid n)) :=
    (memLp_comp_lipschitz (gaussian_inner_pair_law (b i) (b i)).fst.memLp_two
      (hinge_lipschitz ht)).integrable (by norm_num)
  have hfloor : ((RetainedCount θ m : ℕ) : ℝ)/(m : ℝ) ≤ θ := by
    apply (div_le_iff₀ hmR).2
    exact Nat.floor_le (mul_nonneg hθ0 hmR.le)
  have hsum : (m : ℝ)*(∫ z : ℝ, hinge t z ∂gaussianReal 0 1) ≤
      ∑ i, ∫ g : Euclid n, hinge t (inner ℝ (b i) g) ∂stdGaussian (Euclid n) := by
    calc
      _ = ∑ _i : Fin m, ∫ z : ℝ, hinge t z ∂gaussianReal 0 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => gaussian_hinge_expectation_mono (b i) (hb i) ht
  unfold gaussianTrimmingDual
  rw [integral_sub (integrable_const _) ((integrable_finsetSum _ (fun i _ => hInt i)).const_mul _),
    integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_finsetSum _ (fun i _ => hInt i)]
  have hscale := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hmR))
  have hcancel : (1/(m : ℝ))*((m : ℝ)*(∫ z : ℝ, hinge t z ∂gaussianReal 0 1)) =
      ∫ z : ℝ, hinge t z ∂gaussianReal 0 1 := by field_simp [hmR.ne']
  rw [hcancel] at hscale
  have hpop := gaussian_hinge_dual_le hθ0 ha hq ht
  nlinarith [mul_le_mul_of_nonneg_right hfloor ht]

/-- Every actual finite Gaussian trimming dual is square integrable. -/
theorem gaussianTrimmingDual_memLp {m n : ℕ} (θ : ℝ)
    (b : Fin m → Euclid n) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (gaussianTrimmingDual θ b t) 2 (stdGaussian (Euclid n)) := by
  have hmem (i : Fin m) : MemLp (fun g : Euclid n => hinge t (inner ℝ (b i) g)) 2
      (stdGaussian (Euclid n)) :=
    memLp_comp_lipschitz (gaussian_inner_pair_law (b i) (b i)).fst.memLp_two (hinge_lipschitz ht)
  exact (memLp_const _).sub ((memLp_finsetSum _ (fun i _ => hmem i)).const_mul _)

/-- The actual finite Gaussian dual has vanishing variance after the true
retained covariance construction. -/
theorem gaussianTrimmingDual_variance_le {m n r : ℕ} (hm : 0 < m) (θ : ℝ)
    (b : Fin m → Euclid n)
    (hgram : (∑ i, ∑ j, |inner ℝ (b i) (b j)|) ≤ (m : ℝ)^2/Real.sqrt (r+1 : ℕ))
    {t : ℝ} (ht : 0 ≤ t) :
    Var[gaussianTrimmingDual θ b t; stdGaussian (Euclid n)] ≤
      4*t/Real.sqrt (r+1 : ℕ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmem (i : Fin m) : MemLp (fun g : Euclid n => hinge t (inner ℝ (b i) g)) 2
      (stdGaussian (Euclid n)) :=
    memLp_comp_lipschitz (gaussian_inner_pair_law (b i) (b i)).fst.memLp_two (hinge_lipschitz ht)
  have hsum := memLp_finsetSum Finset.univ (fun i _ => hmem i)
  unfold gaussianTrimmingDual
  rw [variance_const_sub (hsum.const_mul _).aestronglyMeasurable, variance_const_mul]
  have hvar := variance_gaussian_rows_hinge_le b ht
  calc
    _ ≤ (1/(m : ℝ))^2 * (4*t*∑ i, ∑ j, |inner ℝ (b i) (b j)|) :=
      mul_le_mul_of_nonneg_left hvar (sq_nonneg _)
    _ ≤ (1/(m : ℝ))^2 * (4*t*((m : ℝ)^2/Real.sqrt (r+1 : ℕ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hgram (by positivity)
    _ = _ := by field_simp [hmR.ne']

#assert_trust kernel gaussianTrimmingDual_memLp
#assert_trust kernel gaussianTrimmingDual_variance_le
#assert_trust kernel gaussian_hinge_expectation_mono
#assert_trust kernel gaussianTrimmingDual_mean_le
#print axioms gaussianTrimmingDual_mean_le
end NLA.Proofs.IE22
