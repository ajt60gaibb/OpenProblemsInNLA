import NLA.IE06.Vendor.SLT.GaussianLipConcen
import NLA.IE06.GaussianSmallest

/-! Gaussian Lipschitz concentration for Mathlib's actual standard Gaussian.
The imported proof is the independently reviewed, pinned SLT proof. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
noncomputable section
namespace NLA.IE06.GaussianConcentration

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

theorem gaussian_measure_eq (n : ℕ) :
    GaussianMeasure.stdGaussianE n = stdGaussian (E n) := by
  exact map_pi_eq_stdGaussian

theorem lipschitz_integrable {n : ℕ} {f : E n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : Integrable f (stdGaussian (E n)) := by
  rw [← gaussian_measure_eq]
  exact GaussianLipConcen.lipschitzE_integrable L.coe_nonneg (by simpa using hf)

theorem lipschitz_upper_tail {n : ℕ} {f : E n → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (x : ℝ) (hx : 0 < x) :
    stdGaussian (E n) {z | (L : ℝ) * sqrt (2*x) <
      f z - ∫ w, f w ∂stdGaussian (E n)} ≤ ENNReal.ofReal (exp (-x)) := by
  by_cases hn : n = 0
  · subst n
    have hc : f = fun _ => f 0 := funext fun z => congrArg f (Subsingleton.elim z 0)
    rw [hc]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]
    have he : {z : E 0 | (L : ℝ) * sqrt (2*x) < 0} = ∅ := by
      ext z
      exact iff_false_intro (not_lt_of_ge (mul_nonneg L.coe_nonneg (sqrt_nonneg _)))
    rw [he, measure_empty]
    exact zero_le
  by_cases hL : L = 0
  · subst L
    have hc : f = fun _ => f 0 := by
      funext z
      apply dist_eq_zero.mp
      have h := hf.dist_le_mul z 0
      simpa using h
    rw [hc]
    simp
  have hLp : 0 < L := pos_iff_ne_zero.mpr hL
  have hLc : 0 < (L : ℝ) := hLp
  have hs : 0 < sqrt (2*x) := sqrt_pos.2 (by positivity)
  have ht : 0 < (L : ℝ) * sqrt (2*x) := mul_pos hLc hs
  have hb := GaussianLipConcen.gaussian_lipschitz_concentration_one_sided
    (Nat.pos_of_ne_zero hn) hLp hf ((L : ℝ) * sqrt (2*x)) ht
  dsimp only at hb
  rw [gaussian_measure_eq] at hb
  have he : -((L : ℝ) * sqrt (2*x))^2 / (2*(L : ℝ)^2) = -x := by
    rw [mul_pow, sq_sqrt (by positivity : 0 ≤ 2*x)]
    field_simp
  rw [he] at hb
  calc
    _ ≤ stdGaussian (E n) {z | (L : ℝ) * sqrt (2*x) ≤
        f z - ∫ w, f w ∂stdGaussian (E n)} := by
      apply measure_mono
      intro z hz
      change (L : ℝ) * sqrt (2*x) < f z - ∫ w, f w ∂stdGaussian (E n) at hz
      change (L : ℝ) * sqrt (2*x) ≤ f z - ∫ w, f w ∂stdGaussian (E n)
      exact le_of_lt hz
    _ ≤ _ := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hb

#assert_trust kernel gaussian_measure_eq
#assert_trust kernel lipschitz_integrable
#assert_trust kernel lipschitz_upper_tail
#print axioms gaussian_measure_eq
#print axioms lipschitz_integrable
#print axioms lipschitz_upper_tail

end NLA.IE06.GaussianConcentration
