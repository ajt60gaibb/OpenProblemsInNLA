import NLA.Proofs.RA10.OperatorMonotoneScalar
import NLA.Proofs.RA10.SpectralFunctionOperations

/-! Normalizing the exact admissible class, without introducing stronger
regularity or matrix assumptions. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open NLA.Statements.RA10

namespace NLA.Proofs.RA10

theorem operatorMonotoneOnNonnegative_smul {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnNonnegative f) {c : ℝ} (hc : 0 ≤ c) :
    OperatorMonotoneOnNonnegative (fun x => c * f x) := by
  intro d hd H G a b QH QG hH hG hHG
  rw [functionMatrix_smul, functionMatrix_smul, ← smul_sub]
  apply (sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mpr
  exact ((sourcePositiveSemidefinite_iff_mathlibPosSemidef _).mp
    (hf d hd H G a b QH QG hH hG hHG)).smul hc

theorem admissibleFunction_smul {f : ℝ → ℝ}
    (hf : AdmissibleFunction f) {c : ℝ} (hc : 0 ≤ c) :
    AdmissibleFunction (fun x => c * f x) :=
  ⟨continuousOn_const.mul hf.1, fun x hx => mul_nonneg hc (hf.2.1 x hx),
    operatorMonotoneOnNonnegative_smul hf.2.2 hc⟩

theorem operatorMonotoneOnNonnegative_add_const {f : ℝ → ℝ}
    (hf : OperatorMonotoneOnNonnegative f) (c : ℝ) :
    OperatorMonotoneOnNonnegative (fun x => f x + c) := by
  intro d hd H G a b QH QG hH hG hHG
  rw [functionMatrix_add, functionMatrix_add,
    functionMatrix_const c a QH hH.2.2.1, functionMatrix_const c b QG hG.2.2.1,
    add_sub_add_right_eq_sub]
  exact hf d hd H G a b QH QG hH hG hHG

/-- The constant endpoint can be removed without losing admissibility. -/
theorem admissibleFunction_sub_zero {f : ℝ → ℝ} (hf : AdmissibleFunction f) :
    AdmissibleFunction (fun x => f x - f 0) := by
  refine ⟨hf.1.sub continuousOn_const, ?_, ?_⟩
  · intro x hx
    exact sub_nonneg.mpr (operatorMonotoneOnNonnegative_monotoneOn hf.2.2
      (show 0 ∈ Set.Ici (0 : ℝ) by simp) hx hx)
  · simpa only [sub_eq_add_neg] using operatorMonotoneOnNonnegative_add_const hf.2.2 (-f 0)

/-- Every nonzero admissible function normalizes at one. The zero case is
separately covered by `admissibleFunction_eq_zero_of_one_eq_zero`. -/
theorem admissibleFunction_normalize {f : ℝ → ℝ} (hf : AdmissibleFunction f)
    (h1 : 0 < f 1) :
    AdmissibleFunction (fun x => (f 1)⁻¹ * f x) ∧ (f 1)⁻¹ * f 1 = 1 :=
  ⟨admissibleFunction_smul hf (inv_nonneg.mpr h1.le), inv_mul_cancel₀ h1.ne'⟩

#assert_trust kernel operatorMonotoneOnNonnegative_smul
#assert_trust kernel admissibleFunction_smul
#assert_trust kernel operatorMonotoneOnNonnegative_add_const
#assert_trust kernel admissibleFunction_sub_zero
#assert_trust kernel admissibleFunction_normalize
#print axioms admissibleFunction_normalize

end NLA.Proofs.RA10
