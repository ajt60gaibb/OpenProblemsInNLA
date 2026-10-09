import ProofProject.CirclePolynomialReflection

/-!
# Division steps for positive circle polynomials

Removing a zero root lowers the circle phase by one. Removing a reflected
pair does the same because its value on the unit circle is `z*|z-a|²`.
All quotient degrees and strict positivity statements are retained explicitly.
-/

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace ProofProject

theorem positiveCirclePhase_div_X {m : ℕ} {p : Polynomial ℂ}
    (hdeg : p.natDegree ≤ 2 * m + 1) (hp0 : p.eval 0 = 0)
    (hp : HasPositiveCirclePhase (m + 1) p) :
    ∃ q : Polynomial ℂ, p = X * q ∧ q.natDegree ≤ 2 * m ∧
      HasPositiveCirclePhase m q := by
  have hdiv : X ∣ p := X_dvd_iff.mpr (by rwa [coeff_zero_eq_eval_zero])
  obtain ⟨q, hq⟩ := hdiv
  have hq0 : q ≠ 0 := by
    intro hh
    apply hp.ne_zero
    rw [hq, hh, mul_zero]
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hq, natDegree_X_mul hq0] at hdeg
    omega
  · intro z hz
    obtain ⟨r, hr, hpr⟩ := hp z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    refine ⟨r, hr, ?_⟩
    apply mul_left_cancel₀ hz0
    calc
      z * q.eval z = z ^ (m + 1) * (r : ℂ) := by
        simpa only [hq, eval_mul, eval_X] using hpr
      _ = z * (z ^ m * (r : ℂ)) := by rw [pow_succ]; ring

/-- A root and its conjugate reciprocal, with the normalization needed for
positive circle values. -/
def circleRootPair (a : ℂ) : Polynomial ℂ :=
  (X - C a) * (1 - C (starRingEnd ℂ a) * X)

theorem circleRootPair_eval (a : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    (circleRootPair a).eval z = z * ((‖z - a‖ ^ 2 : ℝ) : ℂ) := by
  have hzc : z * conj z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  simp only [circleRootPair, eval_mul, eval_sub, eval_X, eval_C, eval_one,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  change (z - a) * (1 - conj a * z) = z * (conj (z - a) * (z - a))
  calc
    _ = (z - a) * (z * conj z - conj a * z) := by rw [hzc]
    _ = _ := by rw [map_sub]; ring

theorem circleRootPair_eq_const_mul (a : ℂ) (ha : a ≠ 0) :
    circleRootPair a = C (-(starRingEnd ℂ a)) *
      ((X - C a) * (X - C ((starRingEnd ℂ a)⁻¹))) := by
  have hca : starRingEnd ℂ a ≠ 0 := by simpa using ha
  have hfactor : (1 : Polynomial ℂ) - C (starRingEnd ℂ a) * X =
      C (-(starRingEnd ℂ a)) * (X - C ((starRingEnd ℂ a)⁻¹)) := by
    rw [mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hca]
    simp only [C_neg, C_1]
    ring
  unfold circleRootPair
  rw [hfactor]
  ring

theorem circleRootPair_natDegree (a : ℂ) (ha : a ≠ 0) :
    (circleRootPair a).natDegree = 2 := by
  have hca : -(starRingEnd ℂ a) ≠ 0 := by simpa using ha
  rw [circleRootPair_eq_const_mul a ha, natDegree_C_mul hca,
    natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    natDegree_X_sub_C, natDegree_X_sub_C]

theorem circleRootPair_ne_zero (a : ℂ) (ha : a ≠ 0) : circleRootPair a ≠ 0 := by
  intro hh
  have hd := circleRootPair_natDegree a ha
  simp [hh] at hd

/-- Two distinct reflected roots divide the polynomial, with the quotient
renormalized to match the positive root-pair factor. -/
theorem circleRootPair_dvd_of_roots {p : Polynomial ℂ} {a : ℂ}
    (ha : 1 < ‖a‖) (hroot : p.eval a = 0)
    (hreflect : p.eval ((starRingEnd ℂ a)⁻¹) = 0) : circleRootPair a ∣ p := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  have hca : starRingEnd ℂ a ≠ 0 := by simpa using ha0
  let b : ℂ := (starRingEnd ℂ a)⁻¹
  have hb : ‖b‖ < 1 := by
    dsimp [b]
    rw [norm_inv]
    change ‖star a‖⁻¹ < 1
    rw [norm_star]
    exact inv_lt_one_of_one_lt₀ ha
  have hba : b ≠ a := by
    intro hh
    rw [hh] at hb
    linarith
  obtain ⟨r, hpr⟩ := (dvd_iff_isRoot.mpr hroot : X - C a ∣ p)
  have hrb : r.eval b = 0 := by
    have he : (b - a) * r.eval b = 0 := by
      simpa only [hpr, eval_mul, eval_sub, eval_X, eval_C] using hreflect
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hba)
  obtain ⟨q₀, hrq⟩ := (dvd_iff_isRoot.mpr hrb : X - C b ∣ r)
  refine ⟨C ((-(starRingEnd ℂ a))⁻¹) * q₀, ?_⟩
  have hu : C (-(starRingEnd ℂ a)) * C ((-(starRingEnd ℂ a))⁻¹) = (1 : Polynomial ℂ) := by
    rw [← C_mul, mul_inv_cancel₀ (neg_ne_zero.mpr hca), C_1]
  calc
    p = ((X - C a) * (X - C b)) * q₀ := by rw [hpr, hrq]; ring
    _ = (C (-(starRingEnd ℂ a)) * C ((-(starRingEnd ℂ a))⁻¹)) *
        (((X - C a) * (X - C b)) * q₀) := by rw [hu, one_mul]
    _ = (C (-(starRingEnd ℂ a)) * ((X - C a) * (X - C b))) *
        (C ((-(starRingEnd ℂ a))⁻¹) * q₀) := by ring
    _ = _ := by rw [circleRootPair_eq_const_mul a ha0]

theorem positiveCirclePhase_div_rootPair {m : ℕ} {p : Polynomial ℂ} {a : ℂ}
    (hdeg : p.natDegree ≤ 2 * (m + 1)) (hp : HasPositiveCirclePhase (m + 1) p)
    (ha : 1 < ‖a‖) (hroot : p.eval a = 0)
    (hreflect : p.eval ((starRingEnd ℂ a)⁻¹) = 0) :
    ∃ q : Polynomial ℂ, p = circleRootPair a * q ∧ q.natDegree ≤ 2 * m ∧
      HasPositiveCirclePhase m q := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨q, hq⟩ := circleRootPair_dvd_of_roots ha hroot hreflect
  have hq0 : q ≠ 0 := by
    intro hh
    apply hp.ne_zero
    rw [hq, hh, mul_zero]
  refine ⟨q, hq, ?_, ?_⟩
  · rw [hq, natDegree_mul (circleRootPair_ne_zero a ha0) hq0,
      circleRootPair_natDegree a ha0] at hdeg
    omega
  · intro z hz
    obtain ⟨r, hr, hpr⟩ := hp z hz
    have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
    have hza : z ≠ a := by
      intro hh
      rw [hh] at hz
      linarith
    have hd : 0 < ‖z - a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hza))
    have hdc : ((‖z - a‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
    refine ⟨r / ‖z - a‖ ^ 2, div_pos hr hd, ?_⟩
    apply mul_left_cancel₀ (mul_ne_zero hz0 hdc)
    calc
      (z * ((‖z - a‖ ^ 2 : ℝ) : ℂ)) * q.eval z = p.eval z := by
        rw [hq, eval_mul, circleRootPair_eval a hz]
      _ = z ^ (m + 1) * (r : ℂ) := hpr
      _ = (z * ((‖z - a‖ ^ 2 : ℝ) : ℂ)) * (z ^ m * ((r / ‖z - a‖ ^ 2 : ℝ) : ℂ)) := by
        rw [pow_succ, Complex.ofReal_div]
        field_simp [hdc]

end ProofProject
