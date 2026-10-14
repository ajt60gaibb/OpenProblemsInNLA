import NLA.Proofs.SP14.EndpointInverseL2Completion
import NLA.Proofs.SP14.FiniteLaurentBackground
import Mathlib.MeasureTheory.Function.L2Space

/-!
The actual finite Laurent correction acting on the completed endpoint inverse.
The Haar integral is normalized to probability measure on the period-`2π`
additive circle. The perturbed background inverse is a later obligation.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open MeasureTheory

namespace NLA.Proofs.SP14

local instance correctionTwoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

/-- The actual finite Laurent correction has the sharp finite coefficient-sum
supremum majorant on the unit circle. -/
theorem finiteLaurentCorrection_norm_le_coeffSum
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (s : Circle) :
    ‖finiteLaurentCorrection u v pMinus pPlus s‖ ≤
      (∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|) := by
  unfold finiteLaurentCorrection negativeLaurent positiveLaurent
  calc
    ‖(∑ j : Fin u, (pMinus j : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))) +
        (∑ j : Fin v, (pPlus j : ℂ) * (s : ℂ) ^ ((j.val + 1 : ℕ) : ℤ))‖ ≤
      ‖∑ j : Fin u, (pMinus j : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))‖ +
      ‖∑ j : Fin v, (pPlus j : ℂ) * (s : ℂ) ^ ((j.val + 1 : ℕ) : ℤ)‖ :=
      norm_add_le _ _
    _ ≤
      (∑ j : Fin u, ‖(pMinus j : ℂ) * (s : ℂ) ^ (-((j.val + 1 : ℕ) : ℤ))‖) +
      (∑ j : Fin v, ‖(pPlus j : ℂ) * (s : ℂ) ^ ((j.val + 1 : ℕ) : ℤ)‖) := by
      gcongr
      · exact norm_sum_le _ _
      · exact norm_sum_le _ _
    _ = (∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|) := by
      simp [norm_zpow, Circle.norm_coe, Complex.norm_real,
        Real.norm_eq_abs]

private theorem endpointInverseL2_integral_norm_sq (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    (∫ θ : AddCircle (2 * Real.pi),
        ‖endpointInverseL2 r hrHalf y θ‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ‖endpointInverseL2 r hrHalf y‖ ^ 2 := by
  let f := endpointInverseL2 r hrHalf y
  have h := congr_arg RCLike.re
    (@L2.inner_def (AddCircle (2 * Real.pi)) ℂ ℂ _ _ _ _ _ f f)
  rw [← integral_re] at h
  · simpa only [← norm_sq_eq_re_inner] using h.symm
  · exact L2.integrable_inner f f

/-- The actual finite correction `P` acting on the completed triangular
inverse has an `L²` energy bound with exact probability-Haar normalization. -/
theorem finiteLaurentCorrection_endpointInverseL2_energy_le
    (r : ℝ) (hrHalf : (1 / 2 : ℝ) < r)
    (u v : ℕ) (pMinus : Fin u → ℝ) (pPlus : Fin v → ℝ)
    (y : SobolevCoeff r) :
    (∫ θ : AddCircle (2 * Real.pi),
       ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) *
         endpointInverseL2 r hrHalf y θ‖ ^ 2
         ∂AddCircle.haarAddCircle) ≤
      ((∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|)) ^ 2 *
        endpointInverseHSBound r ^ 2 * ‖y‖ ^ 2 := by
  let A : ℝ := (∑ j : Fin u, |pMinus j|) + (∑ j : Fin v, |pPlus j|)
  let f := endpointInverseL2 r hrHalf y
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ endpointInverseHSBound r := by
    unfold endpointInverseHSBound
    have hr : 0 < r - 1 / 2 := by linarith
    positivity
  have hfi : Integrable (fun θ : AddCircle (2 * Real.pi) => ‖f θ‖ ^ 2)
      AddCircle.haarAddCircle := by
    exact (Lp.memLp f).integrable_norm_pow (by norm_num)
  have hpoint (θ : AddCircle (2 * Real.pi)) :
      ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) * f θ‖ ^ 2 ≤
        A ^ 2 * ‖f θ‖ ^ 2 := by
    have hP := finiteLaurentCorrection_norm_le_coeffSum
      u v pMinus pPlus (AddCircle.toCircle θ)
    have hmul :
        ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) * f θ‖ ≤
          A * ‖f θ‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    calc
      _ ≤ (A * ‖f θ‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg hA (norm_nonneg _))).2 hmul
      _ = A ^ 2 * ‖f θ‖ ^ 2 := by ring
  have hint :
      (∫ θ : AddCircle (2 * Real.pi),
          ‖finiteLaurentCorrection u v pMinus pPlus (AddCircle.toCircle θ) * f θ‖ ^ 2
            ∂AddCircle.haarAddCircle) ≤
        ∫ θ : AddCircle (2 * Real.pi), A ^ 2 * ‖f θ‖ ^ 2
            ∂AddCircle.haarAddCircle := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
    · exact hfi.const_mul _
    · exact Filter.Eventually.of_forall hpoint
  have hnorm : ‖f‖ ≤ endpointInverseHSBound r * ‖y‖ := by
    exact (endpointInverseL2 r hrHalf).le_opNorm y |>.trans
      (mul_le_mul_of_nonneg_right
        (endpointInverseL2_norm_le r hrHalf) (norm_nonneg y))
  calc
    _ ≤ ∫ θ : AddCircle (2 * Real.pi), A ^ 2 * ‖f θ‖ ^ 2
          ∂AddCircle.haarAddCircle := hint
    _ = A ^ 2 * ‖f‖ ^ 2 := by
      rw [integral_const_mul, endpointInverseL2_integral_norm_sq]
    _ ≤ A ^ 2 * (endpointInverseHSBound r * ‖y‖) ^ 2 := by
      gcongr
    _ = A ^ 2 * endpointInverseHSBound r ^ 2 * ‖y‖ ^ 2 := by ring

#assert_trust kernel finiteLaurentCorrection_norm_le_coeffSum
#print axioms finiteLaurentCorrection_norm_le_coeffSum
#assert_trust kernel finiteLaurentCorrection_endpointInverseL2_energy_le
#print axioms finiteLaurentCorrection_endpointInverseL2_energy_le

end NLA.Proofs.SP14
