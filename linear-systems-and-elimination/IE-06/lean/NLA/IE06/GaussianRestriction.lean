import NLA.IE06.GaussianShift
import NLA.IE06.GaussianLinear

/-! Centered Gaussian restriction to measurable convex symmetric sets.
The directional MGF is proved from the kernel-checked Gaussian shift theorem. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Real Set
open scoped BigOperators ENNReal
noncomputable section
namespace NLA.IE06.GaussianRestriction
open GaussianShift GaussianLinear GaussianQuadratic

def restrictedGaussian {n : ℕ} (K : Set (Fin n → ℝ)) : Measure (Fin n → ℝ) :=
  (gaussianVector n K)⁻¹ • (gaussianVector n).restrict K

theorem restrictedGaussian_probability {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : gaussianVector n K ≠ 0) : IsProbabilityMeasure (restrictedGaussian K) := by
  constructor
  simp only [restrictedGaussian, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hK (measure_ne_top _ _)

theorem complete_square (n : ℕ) (v y : Fin n → ℝ) (t : ℝ) :
    gaussianWeight (y + t • v) * ENNReal.ofReal (exp (t * dot v (y + t • v))) =
      ENNReal.ofReal (exp (t^2 * GaussianShift.squareNorm v / 2)) * gaussianWeight y := by
  unfold gaussianWeight
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← exp_add, ← exp_add]
  congr 1
  have he : -GaussianShift.squareNorm (y + t • v) / 2 + t * dot v (y+t•v) =
      t^2 * GaussianShift.squareNorm v / 2 - GaussianShift.squareNorm y / 2 := by
    calc
      _ = ∑ i, (-(y i + t*v i)^2/2 + t*(v i*(y i+t*v i))) := by
        simp only [GaussianShift.squareNorm, dot, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
        rw [← Finset.sum_div, Finset.sum_neg_distrib]
      _ = ∑ i, (t^2 * (v i)^2/2 - (y i)^2/2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp [GaussianShift.squareNorm, Finset.sum_sub_distrib, Finset.sum_div, Finset.mul_sum]
  linarith

theorem set_lintegral_exp_dot {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : MeasurableSet K) (v : Fin n → ℝ) (t : ℝ) :
    (∫⁻ x in K, ENNReal.ofReal (exp (t * dot v x)) ∂gaussianVector n) =
      ENNReal.ofReal (exp (t^2 * GaussianShift.squareNorm v / 2)) *
        gaussianVector n ((fun x => x+t•v) ⁻¹' K) := by
  classical
  let e : (Fin n → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (exp (t * dot v x))
  have he : Measurable e := by dsimp [e, dot]; fun_prop
  rw [← lintegral_indicator hK, gaussianVector_eq_weight, lintegral_smul_measure,
    smul_eq_mul, lintegral_withDensity_eq_lintegral_mul _ (gaussianWeight_measurable n)
      (he.indicator hK)]
  change normalizer n * (∫⁻ x, gaussianWeight x * K.indicator e x) = _
  rw [← lintegral_add_right_eq_self (fun x => gaussianWeight x * K.indicator e x) (t•v)]
  have hpoint (y : Fin n → ℝ) :
      gaussianWeight (y+t•v) * K.indicator e (y+t•v) =
      ENNReal.ofReal (exp (t^2 * GaussianShift.squareNorm v / 2)) *
        shiftedWeight K (t•v) y := by
    by_cases hy : y+t•v ∈ K
    · simp only [shiftedWeight, Set.indicator, hy,
        show y ∈ (fun x => x+t•v) ⁻¹' K from hy, ↓reduceIte]
      exact complete_square n v y t
    · simp [shiftedWeight, Set.indicator, hy]
  simp_rw [hpoint]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← gaussianVector_eq_weight,
    gaussian_shift_mass hK (t•v)]
  ring

theorem restricted_exp_integrable {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : gaussianVector n K ≠ 0) (v : Fin n → ℝ) (t : ℝ) :
    Integrable (fun x => exp (t * dot v x)) (restrictedGaussian K) := by
  exact (linear_mgf v t).1.restrict.smul_measure (ENNReal.inv_ne_top.mpr hK)

theorem restricted_lintegral_exp_le {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (hK : gaussianVector n K ≠ 0)
    (v : Fin n → ℝ) (t : ℝ) :
    (∫⁻ x, ENNReal.ofReal (exp (t * dot v x)) ∂restrictedGaussian K) ≤
      ENNReal.ofReal (exp (t^2 * GaussianShift.squareNorm v / 2)) := by
  rw [restrictedGaussian, lintegral_smul_measure, smul_eq_mul,
    set_lintegral_exp_dot hm]
  calc
    _ ≤ (gaussianVector n K)⁻¹ *
        (ENNReal.ofReal (exp (t^2 * GaussianShift.squareNorm v / 2)) * gaussianVector n K) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (gaussian_shift_le hm hc hs (t•v)) zero_le) zero_le
    _ = _ := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hK (measure_ne_top _ _), mul_one]

theorem restricted_mgf_le {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (hK : gaussianVector n K ≠ 0)
    (v : Fin n → ℝ) (t : ℝ) :
    (∫ x, exp (t * dot v x) ∂restrictedGaussian K) ≤
      exp (t^2 * GaussianShift.squareNorm v / 2) := by
  apply (ENNReal.ofReal_le_ofReal_iff (exp_pos _).le).mp
  rw [ofReal_integral_eq_lintegral_ofReal (restricted_exp_integrable hK v t)
    (ae_of_all _ (fun _ => (exp_pos _).le))]
  exact restricted_lintegral_exp_le hm hc hs hK v t

theorem restricted_directional_subGaussian {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (hK : gaussianVector n K ≠ 0) :
    SubGaussianQuadratic.DirectionalSubGaussian (restrictedGaussian K) id := by
  intro v
  refine ⟨restricted_exp_integrable hK v, fun t => ?_⟩
  change (∫ x, exp (t * dot v x) ∂restrictedGaussian K) ≤
    exp ((∑ i, v i^2) * t^2 / 2)
  simpa only [GaussianShift.squareNorm, mul_comm (t^2)] using
    restricted_mgf_le hm hc hs hK v t

theorem restricted_quadratic_tail {n b : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (hK : gaussianVector n K ≠ 0)
    (M : Matrix (Fin n) (Fin b) ℝ) (x : ℝ) (hx : 0 ≤ x) :
    restrictedGaussian K {z | (2+4*x) * SubGaussianQuadratic.frobeniusSq M <
      SubGaussianQuadratic.quadratic M z} ≤ ENNReal.ofReal (exp (-x)) := by
  let := restrictedGaussian_probability hK
  exact SubGaussianQuadratic.quadratic_tail measurable_id
    (restricted_directional_subGaussian hm hc hs hK) M x hx

#assert_trust kernel restrictedGaussian
#assert_trust kernel restrictedGaussian_probability
#assert_trust kernel complete_square
#assert_trust kernel set_lintegral_exp_dot
#assert_trust kernel restricted_exp_integrable
#assert_trust kernel restricted_lintegral_exp_le
#assert_trust kernel restricted_mgf_le
#assert_trust kernel restricted_directional_subGaussian
#assert_trust kernel restricted_quadratic_tail

#print axioms restrictedGaussian
#print axioms restrictedGaussian_probability
#print axioms complete_square
#print axioms set_lintegral_exp_dot
#print axioms restricted_exp_integrable
#print axioms restricted_lintegral_exp_le
#print axioms restricted_mgf_le
#print axioms restricted_directional_subGaussian
#print axioms restricted_quadratic_tail

end NLA.IE06.GaussianRestriction
