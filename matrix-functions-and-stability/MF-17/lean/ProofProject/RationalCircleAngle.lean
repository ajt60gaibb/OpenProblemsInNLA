import ProofProject.WeightedPolynomialAngle
import ProofProject.PolynomialLaurent
import ProofProject.ReciprocalPolynomialApproximation

/-! Passing the finite weighted angle to the rational phase of an outer polynomial. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace ProofProject

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def polynomialCircleMap (p : Polynomial ℂ) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun z => p.eval (fourier 1 z), p.continuous.comp (fourier 1).continuous⟩

def polynomialReciprocalCircleMap (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun z => (p.eval (fourier 1 z))⁻¹,
    (p.continuous.comp (fourier 1).continuous).inv₀
      (fun z => hp _ (le_of_eq (finiteCircle_fourier_norm 1 z)))⟩

lemma polynomialCircleMap_reciprocal_tendsto (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) {r : ℕ → Polynomial ℂ}
    (hr : TendstoUniformlyOn (fun N z => (r N).eval z) (fun z => (p.eval z)⁻¹)
      atTop {z | ‖z‖ ≤ 1}) :
    Tendsto (fun N => polynomialCircleMap (r N)) atTop
      (𝓝 (polynomialReciprocalCircleMap p hp)) := by
  apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hr ε hε] with N hN z
  exact hN _ (le_of_eq (finiteCircle_fourier_norm 1 z))

def polynomialCirclePhase (p : Polynomial ℂ) (z : AddCircle (1 : ℝ)) : ℂ :=
  starRingEnd ℂ (p.eval (fourier 1 z)) / p.eval (fourier 1 z)

lemma continuous_polynomialCirclePhase (p : Polynomial ℂ)
    (hp : ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0) : Continuous (polynomialCirclePhase p) :=
  (p.continuous.comp (fourier 1).continuous).star.div
    (p.continuous.comp (fourier 1).continuous)
    (fun z => hp _ (le_of_eq (finiteCircle_fourier_norm 1 z)))

/-- Polynomial reciprocal approximation extends the angle bound without any
loss in its constant. The phase pairing is linear in both analytic factors. -/
theorem polynomialCirclePhase_angle_sq {h : Polynomial ℂ} {K : ℝ}
    (hh : ∀ z : ℂ, ‖z‖ ≤ 1 → h.eval z ≠ 0)
    (hproj : HasPolynomialCircleProjectionBound h K) (hK : 1 ≤ K)
    (a b : Polynomial ℂ) :
    ‖∫ z : AddCircle (1 : ℝ), polynomialCirclePhase h z * a.eval (fourier 1 z) *
        fourier 1 z * b.eval (fourier 1 z) ∂AddCircle.haarAddCircle‖ ^ 2 ≤
      (1 - K⁻¹ ^ 2) *
        (∫ z : AddCircle (1 : ℝ), ‖a.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle) *
        (∫ z : AddCircle (1 : ℝ), ‖b.eval (fourier 1 z)‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  obtain ⟨r, hr⟩ := exists_polynomial_tendstoUniformlyOn_reciprocal h hh
  let A := polynomialCircleMap a
  let B := polynomialCircleMap b
  let H := polynomialCircleMap h
  let R := polynomialReciprocalCircleMap h hh
  let RN := fun N => polynomialCircleMap (r N)
  let U := A * R * H
  let V := (fourier (-1) * star (B * R)) * H
  let UN := fun N => A * RN N * H
  let VN := fun N => (fourier (-1) * star (B * RN N)) * H
  let J : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] PolynomialCircleL2 :=
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
  have htR : Tendsto RN atTop (𝓝 R) := polynomialCircleMap_reciprocal_tendsto h hh hr
  have htU : Tendsto (fun N => J (UN N)) atTop (𝓝 (J U)) :=
    J.continuous.tendsto U |>.comp ((tendsto_const_nhds.mul htR).mul_const H)
  have htV : Tendsto (fun N => J (VN N)) atTop (𝓝 (J V)) :=
    J.continuous.tendsto V |>.comp
      ((tendsto_const_nhds.mul (tendsto_const_nhds.mul htR).star).mul_const H)
  have huN (N : ℕ) : weightedLaurentL2 h (polynomialLaurentCoefficients (a * r N)) =
      J (UN N) := by
    rw [weightedLaurentL2_eq_continuousToLp]
    congr 1
    ext z
    simp only [weightedLaurentFunction, polynomialLaurentCoefficients_eval,
      Polynomial.eval_mul, UN, A, H, RN, polynomialCircleMap, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk]
  have hvN (N : ℕ) : weightedLaurentL2 h (negativePolynomialLaurentCoefficients (b * r N)) =
      J (VN N) := by
    rw [weightedLaurentL2_eq_continuousToLp]
    congr 1
    ext z
    simp only [weightedLaurentFunction, negativePolynomialLaurentCoefficients_eval,
      Polynomial.eval_mul, VN, B, H, RN, polynomialCircleMap, ContinuousMap.mul_apply,
      ContinuousMap.coe_mk, ContinuousMap.star_apply, starRingEnd_apply]
  have hn (N : ℕ) : ‖inner ℂ (J (UN N)) (J (VN N))‖ ^ 2 ≤
      (1 - K⁻¹ ^ 2) * ‖J (UN N)‖ ^ 2 * ‖J (VN N)‖ ^ 2 := by
    rw [← huN, ← hvN]
    apply projectionAngle_sq hK
    exact weightedLaurentL2_projection_line hproj hK _ _
      (polynomialLaurentCoefficients_negative _) (negativePolynomialLaurentCoefficients_nonnegative _)
  have hlim : ‖inner ℂ (J U) (J V)‖ ^ 2 ≤
      (1 - K⁻¹ ^ 2) * ‖J U‖ ^ 2 * ‖J V‖ ^ 2 :=
    le_of_tendsto_of_tendsto ((htU.inner htV).norm.pow 2)
      (((htU.norm.pow 2).const_mul _).mul (htV.norm.pow 2)) (Eventually.of_forall hn)
  have hu (z : AddCircle (1 : ℝ)) : U z = a.eval (fourier 1 z) := by
    change a.eval (fourier 1 z) * (h.eval (fourier 1 z))⁻¹ * h.eval (fourier 1 z) = _
    rw [mul_assoc, inv_mul_cancel₀ (hh _ (le_of_eq (finiteCircle_fourier_norm 1 z))), mul_one]
  have hvnorm (z : AddCircle (1 : ℝ)) : ‖V z‖ = ‖b.eval (fourier 1 z)‖ := by
    change ‖fourier (-1) z * star (b.eval (fourier 1 z) * (h.eval (fourier 1 z))⁻¹) *
      h.eval (fourier 1 z)‖ = _
    rw [norm_mul, norm_mul, finiteCircle_fourier_norm, one_mul, norm_star, norm_mul,
      norm_inv, mul_assoc, inv_mul_cancel₀
        (norm_ne_zero_iff.mpr (hh _ (le_of_eq (finiteCircle_fourier_norm 1 z)))), mul_one]
  have hip : inner ℂ (J U) (J V) = starRingEnd ℂ
      (∫ z : AddCircle (1 : ℝ), polynomialCirclePhase h z * a.eval (fourier 1 z) *
        fourier 1 z * b.eval (fourier 1 z) ∂AddCircle.haarAddCircle) := by
    rw [ContinuousMap.inner_toLp, ← integral_conj]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      dsimp only
      rw [hu]
      change (fourier (-1) z * star (b.eval (fourier 1 z) * (h.eval (fourier 1 z))⁻¹) *
          h.eval (fourier 1 z)) * starRingEnd ℂ (a.eval (fourier 1 z)) = _
      simp only [polynomialCirclePhase, fourier_neg, div_eq_mul_inv,
        starRingEnd_apply, star_mul, star_inv, star_star]
      ring
  rw [hip] at hlim
  simp only [starRingEnd_apply, norm_star] at hlim
  dsimp only [J] at hlim
  rw [circleContinuous_toLp_norm_sq, circleContinuous_toLp_norm_sq] at hlim
  simpa only [hu, hvnorm] using hlim

end ProofProject
