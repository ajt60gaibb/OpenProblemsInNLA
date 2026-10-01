import ProofProject.CirclePolynomialDefs

/-! Conjugate reflection and reciprocal roots of a polynomial with positive circle phase. -/

noncomputable section

open Polynomial
open scoped ComplexConjugate

namespace ProofProject

lemma infinite_complex_unit_circle : Set.Infinite {z : ℂ | ‖z‖ = 1} := by
  have hi : Set.InjOn (fun t : ℝ => (Circle.exp t : ℂ)) (Set.Icc 0 Real.pi) := by
    intro a ha b hb hab
    exact Circle.exp_injOn_Icc (by linarith [Real.pi_pos]) ha hb (Circle.coe_injective hab)
  have h := (Set.Icc_infinite Real.pi_pos).image hi
  exact h.mono (by rintro z ⟨t, ht, rfl⟩; exact Circle.norm_coe _)

namespace HasPositiveCirclePhase

variable {m : ℕ} {p : Polynomial ℂ}

lemma eval_ne_zero (h : HasPositiveCirclePhase m p) {z : ℂ} (hz : ‖z‖ = 1) :
    p.eval z ≠ 0 := by
  obtain ⟨r, hr, he⟩ := h z hz
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ (by intro hzero; simp [hzero] at hz))
    (Complex.ofReal_ne_zero.mpr hr.ne')

lemma ne_zero (h : HasPositiveCirclePhase m p) : p ≠ 0 := by
  intro hp
  have hn := h.eval_ne_zero (z := 1) (by simp)
  simp [hp] at hn

/-- Reciprocal evaluation of the conjugate coefficient reflection. -/
lemma eval_reflect_conj (p : Polynomial ℂ) (N : ℕ) (hd : p.natDegree ≤ N)
    {z : ℂ} (hz : z ≠ 0) :
    (reflect N (p.map (starRingEnd ℂ))).eval ((starRingEnd ℂ z)⁻¹) *
      (starRingEnd ℂ z) ^ N = starRingEnd ℂ (p.eval z) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  let : Invertible (starRingEnd ℂ z) := invertibleOfNonzero hc
  have he := eval₂_reflect_mul_pow (RingHom.id ℂ) (starRingEnd ℂ z) N
    (p.map (starRingEnd ℂ)) (natDegree_map_le.trans hd)
  change (reflect N (p.map (starRingEnd ℂ))).eval (⅟(starRingEnd ℂ z)) *
    (starRingEnd ℂ z) ^ N = (p.map (starRingEnd ℂ)).eval (starRingEnd ℂ z) at he
  simpa only [invOf_eq_inv, eval_map_apply] using he

lemma reflect_conj (h : HasPositiveCirclePhase m p) (hd : p.natDegree ≤ 2 * m) :
    reflect (2 * m) (p.map (starRingEnd ℂ)) = p := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply infinite_complex_unit_circle.mono
  intro z hz
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have hcz0 : starRingEnd ℂ z ≠ 0 := by simpa using hz0
  have hinv : (starRingEnd ℂ z)⁻¹ = z := by rw [← Complex.inv_eq_conj hz, inv_inv]
  have hunit : z * starRingEnd ℂ z = 1 := by
    rw [← Complex.inv_eq_conj hz, mul_inv_cancel₀ hz0]
  have he := eval_reflect_conj p (2 * m) hd hz0
  rw [hinv] at he
  apply mul_right_cancel₀ (pow_ne_zero _ hcz0)
  rw [he]
  obtain ⟨r, hr, hp⟩ := h z hz
  rw [hp, map_mul, map_pow]
  simp only [Complex.conj_ofReal]
  symm
  calc
    (z ^ m * (r : ℂ)) * (starRingEnd ℂ z) ^ (2 * m) =
        (z * starRingEnd ℂ z) ^ m * (starRingEnd ℂ z) ^ m * (r : ℂ) := by
      rw [mul_comm 2 m, pow_mul, pow_two, mul_pow]
      ring
    _ = (starRingEnd ℂ z) ^ m * (r : ℂ) := by rw [hunit, one_pow, one_mul]

lemma coeff_reflection (h : HasPositiveCirclePhase m p) (hd : p.natDegree ≤ 2 * m) :
    p.coeff (2 * m) = starRingEnd ℂ (p.coeff 0) := by
  have he := congrArg (fun q : Polynomial ℂ => q.coeff (2 * m)) (h.reflect_conj hd)
  simpa only [Polynomial.coeff_reflect, revAt_le le_rfl, Nat.sub_self, coeff_map] using he.symm

lemma degree_drop_of_eval_zero {m : ℕ} {p : Polynomial ℂ}
    (h : HasPositiveCirclePhase (m + 1) p) (hd : p.natDegree ≤ 2 * (m + 1))
    (hp0 : p.eval 0 = 0) : p.natDegree ≤ 2 * m + 1 := by
  have hc : p.coeff (2 * (m + 1)) = 0 := by
    rw [h.coeff_reflection hd]
    simp only [coeff_zero_eq_eval_zero, hp0, map_zero]
  have hne : p.natDegree ≠ 2 * (m + 1) := by
    intro he
    rw [← he, coeff_natDegree] at hc
    exact (leadingCoeff_ne_zero.mpr h.ne_zero) hc
  omega

lemma natDegree_eq_of_eval_ne_zero (h : HasPositiveCirclePhase m p)
    (hd : p.natDegree ≤ 2 * m) (hp0 : p.eval 0 ≠ 0) : p.natDegree = 2 * m := by
  apply natDegree_eq_of_le_of_coeff_ne_zero hd
  rw [h.coeff_reflection hd]
  simpa only [coeff_zero_eq_eval_zero, _root_.map_ne_zero] using hp0

lemma reciprocal_root (h : HasPositiveCirclePhase m p) (hd : p.natDegree ≤ 2 * m)
    {z : ℂ} (hz : z ≠ 0) (hpz : p.eval z = 0) :
    p.eval ((starRingEnd ℂ z)⁻¹) = 0 := by
  have he := eval_reflect_conj p (2 * m) hd hz
  rw [h.reflect_conj hd, hpz, map_zero] at he
  exact (mul_eq_zero.mp he).resolve_right (pow_ne_zero _ (by simpa using hz))

lemma exists_outer_reciprocal_roots {m : ℕ} {p : Polynomial ℂ}
    (h : HasPositiveCirclePhase (m + 1) p) (hd : p.natDegree ≤ 2 * (m + 1))
    (hp0 : p.eval 0 ≠ 0) :
    ∃ a : ℂ, 1 < ‖a‖ ∧ p.eval a = 0 ∧ p.eval ((starRingEnd ℂ a)⁻¹) = 0 := by
  have hdeg : 0 < p.natDegree := by rw [h.natDegree_eq_of_eval_ne_zero hd hp0]; omega
  obtain ⟨z, hz⟩ := Complex.exists_root (natDegree_pos_iff_degree_pos.mp hdeg)
  have hz0 : z ≠ 0 := by intro he; subst z; exact hp0 hz
  have hz1 : ‖z‖ ≠ 1 := by intro he; exact h.eval_ne_zero he hz
  rcases lt_or_gt_of_ne hz1 with hlt | hgt
  · have hw := h.reciprocal_root hd hz0 hz
    refine ⟨(starRingEnd ℂ z)⁻¹, ?_, hw, ?_⟩
    · rw [norm_inv, RCLike.norm_conj]
      exact (one_lt_inv₀ (norm_pos_iff.mpr hz0)).mpr hlt
    · simpa only [map_inv₀, starRingEnd_self_apply, inv_inv] using hz.eq_zero
  · exact ⟨z, hgt, hz, h.reciprocal_root hd hz0 hz⟩

end HasPositiveCirclePhase
end ProofProject
