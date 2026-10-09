import ProofProject.CirclePolynomialReflection
import ProofProject.CirclePolynomialDivision

/-!
# Finite factorization of a strictly positive circle weight

The induction removes a zero at the origin or one reciprocal pair of roots.
Only the root outside the closed unit disk is retained in the final factor.
-/

noncomputable section

namespace ProofProject

open Polynomial

private lemma positiveCirclePhase_factor_zero (p : Polynomial ℂ)
    (hdeg : p.natDegree ≤ 0) (hp : HasPositiveCirclePhase 0 p) :
    ∃ h : Polynomial ℂ, h.natDegree ≤ 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) ∧
      ∀ z : ℂ, ‖z‖ = 1 → p.eval z = z ^ 0 * ((‖h.eval z‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨r, hr, hpr⟩ := hp 1 (by simp)
  have hconst := eq_C_of_natDegree_le_zero hdeg
  have hpr' : p.eval 1 = (r : ℂ) := by simpa only [one_pow, one_mul] using hpr
  have hcoeff : p.coeff 0 = (r : ℂ) := by
    simpa only [eval_C] using
      (congrArg (fun q : Polynomial ℂ => q.eval 1) hconst).symm.trans hpr'
  have hpC : p = C (r : ℂ) := hconst.trans (congrArg C hcoeff)
  have hsq : ‖(Real.sqrt r : ℂ)‖ ^ 2 = r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt hr.le]
  refine ⟨C (Real.sqrt r : ℂ), by simp, ?_, ?_⟩
  · intro z _
    simpa only [eval_C, ne_eq, Complex.ofReal_eq_zero] using (Real.sqrt_pos.mpr hr).ne'
  · intro z _
    simp only [hpC, eval_C, pow_zero, one_mul, hsq]

/-- A positive trigonometric polynomial admits a scalar polynomial factor
with no zeros on the closed unit disk and at most half the shifted degree.
The circle identity is exact, with no change of normalization. -/
theorem positiveCirclePhase_factorization (m : ℕ) (p : Polynomial ℂ)
    (hdeg : p.natDegree ≤ 2 * m) (hp : HasPositiveCirclePhase m p) :
    ∃ h : Polynomial ℂ, h.natDegree ≤ m ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0) ∧
      ∀ z : ℂ, ‖z‖ = 1 → p.eval z = z ^ m * ((‖h.eval z‖ ^ 2 : ℝ) : ℂ) := by
  induction m generalizing p with
  | zero => exact positiveCirclePhase_factor_zero p (by simpa using hdeg) hp
  | succ m ih =>
    by_cases hp0 : p.eval 0 = 0
    · have hdrop := hp.degree_drop_of_eval_zero hdeg hp0
      obtain ⟨q, hpq, hqdeg, hq⟩ := positiveCirclePhase_div_X hdrop hp0 hp
      obtain ⟨h, hhdeg, hhnz, hh⟩ := ih q hqdeg hq
      refine ⟨h, hhdeg.trans (Nat.le_succ _), hhnz, ?_⟩
      intro z hz
      rw [hpq, eval_mul, eval_X, hh z hz, pow_succ]
      ring
    · obtain ⟨a, ha, hpa, hpa'⟩ := hp.exists_outer_reciprocal_roots hdeg hp0
      obtain ⟨q, hpq, hqdeg, hq⟩ := positiveCirclePhase_div_rootPair hdeg hp ha hpa hpa'
      obtain ⟨h, hhdeg, hhnz, hh⟩ := ih q hqdeg hq
      refine ⟨(X - C a) * h, ?_, ?_, ?_⟩
      · calc
          _ ≤ (X - C a).natDegree + h.natDegree := natDegree_mul_le
          _ = 1 + h.natDegree := by rw [natDegree_X_sub_C]
          _ ≤ m + 1 := by omega
      · intro z hz
        have hza : z ≠ a := by
          intro heq
          subst z
          linarith
        simpa only [eval_mul, eval_sub, eval_X, eval_C] using
          mul_ne_zero (sub_ne_zero.mpr hza) (hhnz z hz)
      · intro z hz
        rw [hpq, eval_mul, circleRootPair_eval a hz, hh z hz]
        simp only [eval_mul, eval_sub, eval_X, eval_C, norm_mul, mul_pow,
          Complex.ofReal_mul, pow_succ]
        ring

end ProofProject
