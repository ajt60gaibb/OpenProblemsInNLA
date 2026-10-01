import ProofProject.FiniteSchurInterpolation
import ProofProject.OuterToeplitzData
import ProofProject.CirclePolynomialReflection

/-!
# Restricted analytic approximation of an outer polynomial phase

Finite Schur interpolation produces a rational function analytic on a
neighborhood of the closed disk, approximating `conj(h)/h` on the circle
with the exact projection-angle constant. No general Nehari theorem is used.
-/

noncomputable section

namespace ProofProject

open Polynomial Metric

lemma eval_reflect_conj_unit (h : Polynomial ℂ) (m : ℕ)
    (hdeg : h.natDegree ≤ m) {z : ℂ} (hz : ‖z‖ = 1) :
    (reflect m (h.map (starRingEnd ℂ))).eval z =
      z ^ m * starRingEnd ℂ (h.eval z) := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have hcz0 : starRingEnd ℂ z ≠ 0 := by simpa using hz0
  have hinv : (starRingEnd ℂ z)⁻¹ = z := by
    rw [← Complex.inv_eq_conj hz, inv_inv]
  have he := HasPositiveCirclePhase.eval_reflect_conj h m hdeg hz0
  rw [hinv] at he
  calc
    _ = starRingEnd ℂ (h.eval z) / (starRingEnd ℂ z) ^ m :=
      (eq_div_iff (pow_ne_zero _ hcz0)).mpr he
    _ = _ := by rw [← Complex.inv_eq_conj hz]; simp [div_eq_mul_inv, mul_comm]

/-- Combining the two congruences keeps the same polynomial data throughout. -/
lemma exists_phaseSchurRemainder (h p A B : Polynomial ℂ) (m : ℕ) (ρ : ℂ)
    (hdata : X ^ m ∣ reflect m (h.map (starRingEnd ℂ)) - C ρ * h * p)
    (hinterp : X ^ m ∣ A - B * p) :
    ∃ R : Polynomial ℂ,
      B * reflect m (h.map (starRingEnd ℂ)) - C ρ * h * A = X ^ m * R := by
  obtain ⟨U, hU⟩ := hdata
  obtain ⟨V, hV⟩ := hinterp
  refine ⟨B * U - C ρ * h * V, ?_⟩
  calc
    _ = B * (reflect m (h.map (starRingEnd ℂ)) - C ρ * h * p) -
        C ρ * h * (A - B * p) := by ring
    _ = _ := by rw [hU, hV]; ring

/-- The rational remainder has the required exact boundary error. -/
lemma phaseSchurRemainder_error {h A B R : Polynomial ℂ} {m : ℕ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hdeg : h.natDegree ≤ m)
    (hrem : B * reflect m (h.map (starRingEnd ℂ)) - C (ρ : ℂ) * h * A = X ^ m * R)
    {z : ℂ} (hz : ‖z‖ = 1) (hh : h.eval z ≠ 0) (hB : B.eval z ≠ 0)
    (hAB : ‖A.eval z‖ ≤ ‖B.eval z‖) :
    ‖starRingEnd ℂ (h.eval z) / h.eval z - R.eval z / (h.eval z * B.eval z)‖ ≤ ρ := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz
  have he := congrArg (fun p : Polynomial ℂ => p.eval z) hrem
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C,
    eval_reflect_conj_unit h m hdeg hz] at he
  have hid : starRingEnd ℂ (h.eval z) / h.eval z - R.eval z / (h.eval z * B.eval z) =
      (ρ : ℂ) * (z ^ m)⁻¹ * (A.eval z / B.eval z) := by
    field_simp [hh, hB, hz0]
    linear_combination he
  rw [hid, norm_mul, norm_mul, norm_inv, norm_pow, hz, one_pow, inv_one, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ]
  calc
    ρ * ‖A.eval z / B.eval z‖ ≤ ρ * 1 := by
      apply mul_le_mul_of_nonneg_left _ hρ
      rw [norm_div]
      exact (div_le_one (norm_pos_iff.mpr hB)).mpr hAB
    _ = ρ := mul_one _

/-- The finite weighted projection hypothesis supplies the restricted analytic
approximation needed by the source sector argument, with no inflation of `K`. -/
theorem exists_polynomialPhase_analytic_approximation {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 < K) :
    ∃ f : ℂ → ℂ, ∃ r : ℝ, 1 < r ∧
      DifferentiableOn ℂ f (closedBall 0 r) ∧
      ∀ z : ℂ, ‖z‖ = 1 →
        ‖starRingEnd ℂ (h.eval z) / h.eval z - f z‖ ≤ Real.sqrt (1 - K⁻¹ ^ 2) := by
  let m := h.natDegree
  let ρ := Real.sqrt (1 - K⁻¹ ^ 2)
  obtain ⟨p, hpdeg, hpbound, hpdata⟩ := exists_outerToeplitzData hh hproj hK m le_rfl
  obtain ⟨A, B, hB, hAB, hinterp⟩ := exists_finiteSchurInterpolant m p hpbound
  obtain ⟨R, hrem⟩ := exists_phaseSchurRemainder h p A B m (ρ : ℂ) hpdata hinterp
  have hden : ∀ z : ℂ, ‖z‖ ≤ 1 → (h * B).eval z ≠ 0 := by
    intro z hz
    simpa only [eval_mul] using mul_ne_zero (hh z hz) (hB z hz)
  obtain ⟨r, hr, hlarge⟩ := polynomial_exists_zeroFree_larger_disk (h * B) hden
  refine ⟨fun z => R.eval z / (h * B).eval z, r, hr, ?_, ?_⟩
  · intro z hz
    exact (R.differentiableAt.div (h * B).differentiableAt
      (hlarge z (by simpa using hz))).differentiableWithinAt
  · intro z hz
    simpa only [eval_mul] using phaseSchurRemainder_error (Real.sqrt_nonneg _)
      le_rfl hrem hz (hh z hz.le) (hB z hz.le) (hAB z hz.le)

end ProofProject
