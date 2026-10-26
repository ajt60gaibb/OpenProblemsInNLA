import NLA.Proofs.TR06.ModelSemantics
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! The literal individual-normalization derivative in the intrinsic boundary. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.TR06.Model
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Individual normalization, as a vector-valued map. -/
def normalize (x : E) : E := ‖x‖⁻¹ • x

/-- Its actual derivative, expressed using the continuous inner-product map. -/
def normalizationDerivative (a : E) : E →L[ℝ] E :=
  ‖a‖⁻¹ • ContinuousLinearMap.id ℝ E -
    ((‖a‖^3)⁻¹ • innerSL ℝ a).smulRight a

theorem hasFDerivAt_norm_actual (a : E) (ha : a ≠ 0) :
    HasFDerivAt (fun x : E => ‖x‖) (‖a‖⁻¹ • innerSL ℝ a) a := by
  have h := (hasStrictFDerivAt_norm_sq a).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr ha))
  have hf : (fun x : E => Real.sqrt (‖x‖^2)) = (fun x : E => ‖x‖) :=
    funext (fun x => Real.sqrt_sq (norm_nonneg x))
  rw [hf] at h
  have hc : (1 / (2 * ‖a‖)) * 2 = ‖a‖⁻¹ := by field_simp
  have he : (1 / (2 * ‖a‖)) • (2 • innerSL ℝ a) = ‖a‖⁻¹ • innerSL ℝ a := by
    ext v
    simp
    field_simp
  simpa only [Real.sqrt_sq (norm_nonneg a),he] using h

theorem hasFDerivAt_normalize (a : E) (ha : a ≠ 0) :
    HasFDerivAt normalize (normalizationDerivative a) a := by
  have h := ((hasDerivAt_inv (norm_ne_zero_iff.mpr ha)).comp_hasFDerivAt a (hasFDerivAt_norm_actual a ha)).smul
    (hasFDerivAt_id a)
  convert! h using 1
  ext v
  simp [normalizationDerivative,ContinuousLinearMap.smulRight_apply,smul_smul]
  module

variable {d : ℕ} {n : Fin d → ℕ}

theorem normalizationDerivative_eq_variation (a v : NLA.TR06.Tensor ℝ d n) :
    normalizationDerivative a v = NLA.Statements.TR06.NormalizeVariation a v := by
  simp [normalizationDerivative,NLA.Statements.TR06.NormalizeVariation,
    ContinuousLinearMap.smulRight_apply,div_eq_mul_inv,mul_comm]

theorem fderiv_normalize_apply (a v : NLA.TR06.Tensor ℝ d n) (ha : a ≠ 0) :
    fderiv ℝ normalize a v = NLA.Statements.TR06.NormalizeVariation a v := by
  rw [(hasFDerivAt_normalize a ha).fderiv,normalizationDerivative_eq_variation]

#assert_trust kernel hasFDerivAt_norm_actual
#assert_trust kernel hasFDerivAt_normalize
#assert_trust kernel normalizationDerivative_eq_variation
#assert_trust kernel fderiv_normalize_apply
#print axioms hasFDerivAt_normalize
#print axioms fderiv_normalize_apply
end NLA.Proofs.TR06.Model
