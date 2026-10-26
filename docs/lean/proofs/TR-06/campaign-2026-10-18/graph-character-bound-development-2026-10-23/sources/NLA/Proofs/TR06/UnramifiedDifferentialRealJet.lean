/-
Copyright (c) 2026. Released under Apache 2.0 license.
The actual real pivot derivative produces the same complex algebraic jet.
-/
import NLA.Proofs.TR06.UnramifiedDifferentialJet
import NLA.TR06.SegreNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open NLA.TR06 NLA.TR06.Segre
namespace NLA.Proofs.TR06.UnramifiedDifferential

variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ} {q₀ : Fin r → TensorIndex d n}

theorem contDiff_real_pivot_polynomial (p : MvPolynomial (Coordinate q₀) ℝ)
    (k : WithTop ℕ∞) :
    ContDiff ℝ k (fun z : Parameter ℝ q₀ => MvPolynomial.eval (fun c => z c) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℝ k (fun _ : Parameter ℝ q₀ => c))
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p c hp =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
      hp.mul (contDiff_piLp_apply (p := 2) (i := c))

theorem differentiable_real_pivot_sum (q₀ : Fin r → TensorIndex d n) :
    Differentiable ℝ (sum (𝕜 := ℝ) q₀) := by
  apply (differentiable_piLp (p := 2)).mpr
  intro q
  have hp := (contDiff_real_pivot_polynomial (sumPolynomial ℝ q₀ q) 1).differentiable one_ne_zero
  simpa only [eval_sumPolynomial] using hp

@[simp] theorem complexParameter_affine_line (q₀ : Fin r → TensorIndex d n)
    (z v : Parameter ℝ q₀) (t : ℝ) :
    complexParameter q₀ (z+t•v) = complexParameter q₀ z + (t : ℂ) • complexParameter q₀ v := by
  ext c
  simp [complexParameter, smul_eq_mul]

/-- Actual real derivative-kernel vectors annihilate the complex coordinate
jets after literal scalar extension; no equality of real/complex tensor ranks
is asserted or used. -/
theorem pivotJet_sum_zero_of_real_fderiv_eq_zero (q₀ : Fin r → TensorIndex d n)
    (z v : Parameter ℝ q₀) (hv : fderiv ℝ (sum q₀) z v = 0) :
    ∀ q, (pivotJet (complexParameter q₀ z) (complexParameter q₀ v)
      (sumPolynomial ℂ q₀ q)).snd = 0 := by
  have hl : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
  have hf : HasFDerivAt (sum q₀) (fderiv ℝ (sum q₀) z) (z+(0:ℝ)•v) := by
    simpa using (differentiable_real_pivot_sum q₀ z).hasFDerivAt
  have hs := hf.comp_hasDerivAt 0 hl
  simp only [hv] at hs
  intro q
  have hq := (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : TensorIndex d n => ℝ) q).hasFDerivAt.comp_hasDerivAt 0 hs
  have hreal := hq.ofReal_comp
  have hcomplex := (hasDerivAt_pivot_polynomial_line (sumPolynomial ℂ q₀ q)
    (complexParameter q₀ z) (complexParameter q₀ v)).comp_ofReal
  have heq : (fun t : ℝ => MvPolynomial.eval
      (fun c => (complexParameter q₀ z + (t : ℂ) • complexParameter q₀ v) c)
      (sumPolynomial ℂ q₀ q)) = (fun t : ℝ => (sum q₀ (z+t•v) q : ℂ)) := by
    funext t
    rw [← complexParameter_affine_line, eval_sumPolynomial, sum_complexParameter]
    rfl
  rw [heq] at hcomplex
  simpa using hcomplex.unique hreal

#print axioms differentiable_real_pivot_sum
#print axioms pivotJet_sum_zero_of_real_fderiv_eq_zero
#assert_trust kernel differentiable_real_pivot_sum
#assert_trust kernel pivotJet_sum_zero_of_real_fderiv_eq_zero
end NLA.Proofs.TR06.UnramifiedDifferential
