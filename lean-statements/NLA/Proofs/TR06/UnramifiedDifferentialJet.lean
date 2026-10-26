/-
Copyright (c) 2026. Released under Apache 2.0 license.
The actual algebraic jet equals the directional analytic derivative.
-/
import NLA.Proofs.TR06.UnramifiedDifferentialCoordinates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.TR06 NLA.TR06.Segre
namespace NLA.Proofs.TR06.UnramifiedDifferential

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ} {q₀ : Fin r → TensorIndex d n}

/-- Actual evaluation of every pivot polynomial is a smooth complex map. -/
theorem contDiff_pivot_polynomial (p : MvPolynomial (Coordinate q₀) ℂ)
    (k : WithTop ℕ∞) :
    ContDiff ℂ k (fun z : Parameter ℂ q₀ => MvPolynomial.eval (fun c => z c) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℂ k (fun _ : Parameter ℂ q₀ => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p c hp =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
      hp.mul (contDiff_piLp_apply (p := 2) (i := c))

/-- The genuine first jet gives the derivative along the actual affine line. -/
theorem hasDerivAt_pivot_polynomial_line
    (p : MvPolynomial (Coordinate q₀) ℂ) (z v : Parameter ℂ q₀) :
    HasDerivAt (fun t : ℂ => MvPolynomial.eval (fun c => (z + t • v) c) p)
      (pivotJet z v p).snd 0 := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa only [MvPolynomial.eval_C, pivotJet_C, TrivSqZeroExt.snd_inl] using
        (hasDerivAt_const (0 : ℂ) c)
  | add p q hp hq =>
    convert hp.add hq using 1 <;> try rfl
    · funext t
      simp only [MvPolynomial.eval_add, Pi.add_apply]
    · exact pivotJet_add_snd z v p q
  | mul_X p c hp =>
    have hc : HasDerivAt (fun t : ℂ => z c + t * v c) (v c) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v c)).const_add (z c)
    have h := hp.mul hc
    convert h using 1 <;> try rfl
    · ext t
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, Pi.mul_apply]
    · rw [pivotJet_mul_snd, pivotJet_X]
      simp only [TrivSqZeroExt.snd_mk, MvPolynomial.eval_X, zero_mul, add_zero,
        zero_smul]
      ring

/-- The actual tensor-valued addition map is differentiable everywhere. -/
theorem differentiable_pivot_sum (q₀ : Fin r → TensorIndex d n) :
    Differentiable ℂ (sum (𝕜 := ℂ) q₀) := by
  apply (differentiable_piLp (p := 2)).mpr
  intro q
  have hp := (contDiff_pivot_polynomial (sumPolynomial ℂ q₀ q) 1).differentiable one_ne_zero
  simpa only [eval_sumPolynomial] using hp

/-- A vector killed by the actual Fréchet addition derivative gives a zero
jet on each actual addition coordinate polynomial. -/
theorem pivotJet_sum_zero_of_fderiv_eq_zero (q₀ : Fin r → TensorIndex d n)
    (z v : Parameter ℂ q₀) (hv : fderiv ℂ (sum q₀) z v = 0) :
    ∀ q, (pivotJet z v (sumPolynomial ℂ q₀ q)).snd = 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
  have hf : HasFDerivAt (sum q₀) (fderiv ℂ (sum q₀) z) (z + (0 : ℂ) • v) := by
    simpa using (differentiable_pivot_sum q₀ z).hasFDerivAt
  have hs := hf.comp_hasDerivAt 0 hl
  simp only [hv] at hs
  intro q
  have hq := (PiLp.proj (𝕜 := ℂ) (p := 2) (β := fun _ : TensorIndex d n => ℂ) q).hasFDerivAt.comp_hasDerivAt 0 hs
  have hp := hasDerivAt_pivot_polynomial_line (sumPolynomial ℂ q₀ q) z v
  simp only [eval_sumPolynomial] at hp
  have he := hp.unique hq
  simpa using he

#print axioms contDiff_pivot_polynomial
#print axioms hasDerivAt_pivot_polynomial_line
#print axioms differentiable_pivot_sum
#print axioms pivotJet_sum_zero_of_fderiv_eq_zero
#assert_trust kernel contDiff_pivot_polynomial
#assert_trust kernel hasDerivAt_pivot_polynomial_line
#assert_trust kernel differentiable_pivot_sum
#assert_trust kernel pivotJet_sum_zero_of_fderiv_eq_zero
end NLA.Proofs.TR06.UnramifiedDifferential
