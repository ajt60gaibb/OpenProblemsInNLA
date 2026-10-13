import NLA.Proofs.SP14.EndpointInverseL2FiniteSupportMap

/-!
The actual finite triangular inverse extends uniquely from finite-support
weighted coefficients to probability-Haar `L²` on the circle of period `2π`.
No pointwise value is assigned to a general `L²` class.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

local instance completionTwoPiPositive : Fact (0 < 2 * Real.pi) :=
  ⟨Real.two_pi_pos⟩

private theorem endpointFiniteSupportInverse_bound (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    ∀ y : endpointFiniteSupport r,
      ‖endpointFiniteSupportInverse r y‖ ≤
        endpointInverseHSBound r * ‖(endpointFiniteSupport r).subtype y‖ := by
  intro y
  simpa using endpointFiniteSupportInverse_norm_le r hrHalf y

/-- The source's actual triangular inverse, completed from finite polynomial
inputs to a bounded complex-linear probability-Haar `L²` operator. -/
noncomputable def endpointInverseL2 (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    SobolevCoeff r →L[ℂ]
      MeasureTheory.Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * Real.pi)) :=
  (endpointFiniteSupportInverse r).extendOfNorm
    (endpointFiniteSupport r).subtype

/-- The completed inverse agrees exactly with the source's finite triangular
inverse on the literal first-`N` weighted truncation. -/
theorem endpointInverseL2_truncation (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    endpointInverseL2 r hrHalf (sobolevTruncation r N y) =
      endpointFiniteInverseLp r y N := by
  change (endpointFiniteSupportInverse r).extendOfNorm
      (endpointFiniteSupport r).subtype
      ((endpointFiniteSupport r).subtype
        (endpointFiniteSupportTruncation r N y)) =
      endpointFiniteInverseLp r y N
  rw [LinearMap.extendOfNorm_eq (endpointFiniteSupport_dense r)
    ⟨endpointInverseHSBound r, endpointFiniteSupportInverse_bound r hrHalf⟩]
  exact endpointFiniteSupportInverse_truncation r y N

/-- The operator norm retains the exact sufficient source constant
`B_r = 1 + 1/(r-1/2)` for every `r>1/2`. -/
theorem endpointInverseL2_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) :
    ‖endpointInverseL2 r hrHalf‖ ≤ endpointInverseHSBound r := by
  have hB : 0 ≤ endpointInverseHSBound r := by
    unfold endpointInverseHSBound
    have hr : 0 < r - 1 / 2 := by linarith
    positivity
  exact LinearMap.opNorm_extendOfNorm_le
    (endpointFiniteSupport_dense r) hB
    (endpointFiniteSupportInverse_bound r hrHalf)

/-- Actual finite inverse polynomials converge in normalized-circle `L²`
to the completed bounded inverse. -/
theorem endpointFiniteInverseLp_tendsto (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) :
    Filter.Tendsto (fun N : ℕ => endpointFiniteInverseLp r y N)
      Filter.atTop (nhds (endpointInverseL2 r hrHalf y)) := by
  have h := ((endpointInverseL2 r hrHalf).continuous.tendsto y).comp
    (tendsto_sobolevTruncation r y)
  have heq : (fun N : ℕ => endpointFiniteInverseLp r y N) =
      (fun N : ℕ => endpointInverseL2 r hrHalf (sobolevTruncation r N y)) := by
    funext N
    exact (endpointInverseL2_truncation r hrHalf y N).symm
  rw [heq]
  simpa only [Function.comp_def] using h

#assert_trust kernel endpointInverseL2_truncation
#print axioms endpointInverseL2_truncation
#assert_trust kernel endpointInverseL2_norm_le
#print axioms endpointInverseL2_norm_le
#assert_trust kernel endpointFiniteInverseLp_tendsto
#print axioms endpointFiniteInverseLp_tendsto

end NLA.Proofs.SP14
