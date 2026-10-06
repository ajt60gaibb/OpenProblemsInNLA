import Mathlib
import NLA.IE06.Vendor.Isoperimetric.PrekopaLeindler
import NLA.IE06.GaussianShiftGeometry
import NLA.IE06.GaussianSmallest

set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory MeasureTheory.Measure Real Set
open scoped BigOperators ENNReal
noncomputable section
namespace NLA.IE06.GaussianShift

theorem lintegral_half_smul {n : ℕ} {f : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ x, f ((1 / 2 : ℝ) • x)) = (2 : ℝ≥0∞)^n * ∫⁻ x, f x := by
  rw [← lintegral_map hf (by fun_prop)]
  rw [map_addHaar_smul volume (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  rw [lintegral_smul_measure]
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul]
  congr 1
  rw [← inv_pow, one_div, inv_inv, abs_of_nonneg (by positivity),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

theorem half_factor (n : ℕ) :
    (ENNReal.ofReal ((1 - (1 / 2 : ℝ)) ^ ((n:ℝ) * (1 - 1 / 2)) *
      (1 / 2 : ℝ) ^ ((n:ℝ) * (1 / 2))))⁻¹ = (2:ℝ≥0∞)^n := by
  norm_num only [show (1:ℝ) - 1/2 = 1/2 by norm_num]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 1/2)]
  rw [show (n:ℝ)*(1/2) + (n:ℝ)*(1/2) = n by ring, Real.rpow_natCast]
  rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2), ENNReal.inv_pow]
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 1/2)]
  norm_num

theorem midpoint_prekopa {d : ℕ} {f g h : (Fin (d+1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hmid : ∀ x y, f x ^ (1/2:ℝ) * g y ^ (1/2:ℝ) ≤ h ((1/2:ℝ) • (x+y))) :
    (∫⁻ x, f x) ^ (1/2:ℝ) * (∫⁻ x, g x) ^ (1/2:ℝ) ≤ ∫⁻ x, h x := by
  have hp := PrekopaLeindler.prekopa_leindler
    (θ := (1/2:ℝ)) (f := f) (g := g) (h := fun z => h ((1/2:ℝ) • z))
    ⟨by norm_num, by norm_num, hf, hg, by fun_prop, by simpa only [show (1:ℝ)-1/2=1/2 by norm_num] using hmid⟩
  rw [lintegral_half_smul hh] at hp
  have hc : (ENNReal.ofReal
      ((1 - (1 / 2 : ℝ)) ^ (((d:ℝ) + 1) * (1 - 1 / 2)) *
      (1 / 2 : ℝ) ^ (((d:ℝ) + 1) * (1 / 2))))⁻¹ = (2:ℝ≥0∞)^(d+1) := by
    simpa using half_factor (d+1)
  rw [ENNReal.ofReal_inv_of_pos (by positivity), hc] at hp
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num] at hp
  rw [mul_assoc] at hp
  exact (ENNReal.mul_le_mul_iff_right (by positivity) (by finiteness)).mp hp



def squareNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

def gaussianWeight {n : ℕ} (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (exp (-squareNorm x / 2))

theorem gaussianWeight_measurable (n : ℕ) :
    Measurable (gaussianWeight (n := n)) := by
  unfold gaussianWeight squareNorm
  fun_prop

theorem gaussianWeight_neg {n : ℕ} (x : Fin n → ℝ) :
    gaussianWeight (-x) = gaussianWeight x := by simp [gaussianWeight, squareNorm]

theorem gaussianWeight_midpoint {n : ℕ} (x y : Fin n → ℝ) :
    gaussianWeight x ^ (1/2:ℝ) * gaussianWeight y ^ (1/2:ℝ) ≤
      gaussianWeight ((1/2:ℝ) • (x+y)) := by
  unfold gaussianWeight
  rw [ENNReal.ofReal_rpow_of_pos (exp_pos _), ENNReal.ofReal_rpow_of_pos (exp_pos _)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← exp_mul, ← exp_mul, ← exp_add]
  apply exp_le_exp.mpr
  have hs : squareNorm ((1/2:ℝ) • (x+y)) ≤ (squareNorm x + squareNorm y) / 2 := by
    unfold squareNorm
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i _
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    nlinarith [sq_nonneg (x i - y i)]
  linarith

def shiftedWeight {n : ℕ} (K : Set (Fin n → ℝ)) (v : Fin n → ℝ) :
    (Fin n → ℝ) → ℝ≥0∞ :=
  (fun x => x+v) ⁻¹' K |>.indicator gaussianWeight

theorem shiftedWeight_measurable {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : MeasurableSet K) (v : Fin n → ℝ) : Measurable (shiftedWeight K v) :=
  (gaussianWeight_measurable n).indicator (hK.preimage (by fun_prop))

theorem shiftedWeight_reflection {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : GaussianShiftGeometry.CentrallySymmetric K) (v x : Fin n → ℝ) :
    shiftedWeight K (-v) (-x) = shiftedWeight K v x := by
  classical
  have he : -x + -v ∈ K ↔ x+v ∈ K := by
    simpa only [neg_add] using (hK (x+v)).symm
  unfold shiftedWeight
  change (if -x + -v ∈ K then gaussianWeight (-x) else 0) =
    if x+v ∈ K then gaussianWeight x else 0
  rw [he, gaussianWeight_neg]

theorem shiftedWeight_integral_reflection {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : GaussianShiftGeometry.CentrallySymmetric K) (v : Fin n → ℝ) :
    (∫⁻ x, shiftedWeight K (-v) x) = ∫⁻ x, shiftedWeight K v x := by
  rw [← lintegral_neg_eq_self (shiftedWeight K (-v))]
  simp only [shiftedWeight_reflection hK]

theorem shiftedWeight_midpoint {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : Convex ℝ K) (v x y : Fin n → ℝ) :
    shiftedWeight K v x ^ (1/2:ℝ) * shiftedWeight K (-v) y ^ (1/2:ℝ) ≤
      shiftedWeight K 0 ((1/2:ℝ) • (x+y)) := by
  by_cases hx : x+v ∈ K
  · by_cases hy : y + -v ∈ K
    · have hm : (1/2:ℝ) • (x+y) ∈ K := by
        have := hK.midpoint_mem hx hy
        have he : midpoint ℝ (x+v) (y + -v) = (1/2:ℝ) • (x+y) := by
          simp only [midpoint_eq_smul_add, invOf_eq_inv, one_div]
          congr 1
          abel
        rwa [he] at this
      simpa only [shiftedWeight, Set.indicator, Set.mem_preimage, hx, hy, add_zero,
        hm, ↓reduceIte] using gaussianWeight_midpoint x y
    · simp [shiftedWeight, hx, hy]
  · simp [shiftedWeight, hx]

theorem gaussian_weight_shift_le {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (v : Fin n → ℝ) :
    (∫⁻ x, shiftedWeight K v x) ≤ ∫⁻ x, shiftedWeight K 0 x := by
  cases n with
  | zero =>
      have hv : v = 0 := Subsingleton.elim _ _
      rw [hv]
  | succ d =>
      have h := midpoint_prekopa (shiftedWeight_measurable hm v)
        (shiftedWeight_measurable hm (-v)) (shiftedWeight_measurable hm 0)
        (shiftedWeight_midpoint hc v)
      rw [shiftedWeight_integral_reflection hs v,
        ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num : (0:ℝ)≤1/2)
          (by norm_num : (0:ℝ)≤1/2)] at h
      norm_num at h
      exact h



def normalizer (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal ((sqrt (2 * π) ^ n)⁻¹)

theorem normalizer_ne_zero (n : ℕ) : normalizer n ≠ 0 := by
  unfold normalizer
  positivity

theorem normalizer_ne_top (n : ℕ) : normalizer n ≠ ⊤ := ENNReal.ofReal_ne_top

theorem gaussianVector_eq_weight (n : ℕ) :
    GaussianQuadratic.gaussianVector n =
      normalizer n • (volume : Measure (Fin n → ℝ)).withDensity gaussianWeight := by
  rw [GaussianQuadratic.gaussianVector, GaussianSmallest.pi_gaussian_density]
  have he : (fun x : Fin n → ℝ => ENNReal.ofReal
      (∏ i : Fin n, ProbabilityTheory.gaussianPDFReal 0 1 (x i))) =
      normalizer n • gaussianWeight := by
    funext x
    rw [GaussianSmallest.product_density]
    simp only [GaussianSmallest.density, EuclideanSpace.real_norm_sq_eq,
      Pi.smul_apply, smul_eq_mul, normalizer, gaussianWeight, squareNorm]
    exact ENNReal.ofReal_mul (by positivity)
  rw [he, withDensity_smul _ (gaussianWeight_measurable n)]
  rfl

theorem gaussian_shift_mass {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (v : Fin n → ℝ) :
    GaussianQuadratic.gaussianVector n ((fun x => x+v) ⁻¹' K) =
      normalizer n * ∫⁻ x, shiftedWeight K v x := by
  rw [gaussianVector_eq_weight, Measure.smul_apply, smul_eq_mul,
    withDensity_apply _ (hm.preimage (by fun_prop))]
  rw [shiftedWeight, lintegral_indicator (hm.preimage (by fun_prop))]

theorem gaussian_shift_le {n : ℕ} {K : Set (Fin n → ℝ)}
    (hm : MeasurableSet K) (hc : Convex ℝ K)
    (hs : GaussianShiftGeometry.CentrallySymmetric K) (v : Fin n → ℝ) :
    GaussianQuadratic.gaussianVector n ((fun x => x+v) ⁻¹' K) ≤
      GaussianQuadratic.gaussianVector n K := by
  have h0 : GaussianQuadratic.gaussianVector n K =
      normalizer n * ∫⁻ x, shiftedWeight K 0 x := by
    simpa using gaussian_shift_mass hm (0 : Fin n → ℝ)
  rw [gaussian_shift_mass hm v, h0]
  exact mul_le_mul_of_nonneg_left (gaussian_weight_shift_le hm hc hs v) zero_le

#assert_trust kernel lintegral_half_smul
#assert_trust kernel half_factor
#assert_trust kernel midpoint_prekopa
#assert_trust kernel squareNorm
#assert_trust kernel gaussianWeight
#assert_trust kernel gaussianWeight_measurable
#assert_trust kernel gaussianWeight_neg
#assert_trust kernel gaussianWeight_midpoint
#assert_trust kernel shiftedWeight
#assert_trust kernel shiftedWeight_measurable
#assert_trust kernel shiftedWeight_reflection
#assert_trust kernel shiftedWeight_integral_reflection
#assert_trust kernel shiftedWeight_midpoint
#assert_trust kernel gaussian_weight_shift_le
#assert_trust kernel normalizer
#assert_trust kernel normalizer_ne_zero
#assert_trust kernel normalizer_ne_top
#assert_trust kernel gaussianVector_eq_weight
#assert_trust kernel gaussian_shift_mass
#assert_trust kernel gaussian_shift_le

#print axioms lintegral_half_smul
#print axioms half_factor
#print axioms midpoint_prekopa
#print axioms squareNorm
#print axioms gaussianWeight
#print axioms gaussianWeight_measurable
#print axioms gaussianWeight_neg
#print axioms gaussianWeight_midpoint
#print axioms shiftedWeight
#print axioms shiftedWeight_measurable
#print axioms shiftedWeight_reflection
#print axioms shiftedWeight_integral_reflection
#print axioms shiftedWeight_midpoint
#print axioms gaussian_weight_shift_le
#print axioms normalizer
#print axioms normalizer_ne_zero
#print axioms normalizer_ne_top
#print axioms gaussianVector_eq_weight
#print axioms gaussian_shift_mass
#print axioms gaussian_shift_le

end NLA.IE06.GaussianShift
