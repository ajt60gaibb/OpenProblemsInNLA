/-
Copyright (c) 2026. Released under Apache 2.0 license.
The actual positive-radius character at real, nonzero pivot data.
-/
import NLA.Proofs.TR06.GraphCharacterAlgebra
import NLA.TR06.SegreNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR06.GraphCharacter
open NLA.TR06 NLA.TR06.Segre GraphAlgebra
variable {d : ℕ} {n : Fin d → ℕ} {r : ℕ}

/-- Actual real pivot coordinates and the positive Euclidean summand radii,
viewed as complex polynomial values. -/
def realCoordinates (q₀ : Fin r → TensorIndex d n) (z : Parameter ℝ q₀) : Variable q₀ → ℂ :=
  Sum.elim (fun c => (z c : ℂ)) (fun i => (‖summands q₀ z i‖ : ℂ))

@[simp] theorem polynomialCharacter_real_summand (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (i : Fin r) (q : TensorIndex d n) :
    polynomialCharacter q₀ (realCoordinates q₀ z) (summand q₀ i q) =
      (summands q₀ z i q : ℂ) := by
  unfold polynomialCharacter summand
  rw [MvPolynomial.aeval_rename]
  change MvPolynomial.eval (fun c => complexParameter q₀ z c)
    (summandPolynomial ℂ q₀ i q) = _
  rw [eval_summandPolynomial]
  simp only [summands,pureTensor,PiLp.smul_apply,smul_eq_mul,
    factor_complexParameter,Complex.ofReal_mul,Complex.ofReal_prod]
  rfl

/-- The actual norm satisfies every literal radius-square equation. -/
theorem realCoordinates_radiusEquation (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (i : Fin r) :
    polynomialCharacter q₀ (realCoordinates q₀ z) (radiusEquation q₀ i) = 0 := by
  simp only [radiusEquation,map_sub,map_pow,map_sum,polynomialCharacter_real_summand]
  have h : (‖summands q₀ z i‖ : ℂ)^2 = ∑ q, (summands q₀ z i q : ℂ)^2 := by
    exact_mod_cast EuclideanSpace.real_norm_sq_eq (summands q₀ z i)
  simpa only [polynomialCharacter,radius,MvPolynomial.aeval_X,realCoordinates,Sum.elim_inr,
    sub_eq_zero] using h

theorem summands_ne_zero (q₀ : Fin r → TensorIndex d n) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0) (i : Fin r) : summands q₀ z i ≠ 0 := by
  intro h
  have hv := congrArg (fun a : Tensor ℝ d n => a (q₀ i)) h
  exact hz i (by simpa only [summands_pivot,PiLp.zero_apply] using hv)

/-- The actual character, with its positive radius and nonzero localization
denominator proved from real nonzero amplitudes. -/
def character (q₀ : Fin r → TensorIndex d n) (z : Parameter ℝ q₀)
    (hz : ∀ i, z ⟨i,none⟩ ≠ 0) : Source q₀ →ₐ[ℂ] ℂ :=
  characterFromValues q₀ (realCoordinates q₀ z) (realCoordinates_radiusEquation q₀ z)
    (fun i => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (summands_ne_zero q₀ z hz i)))

@[simp] theorem character_source_variable (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz) (c : Coordinate q₀) :
    character q₀ z hz (sourceHom q₀ (MvPolynomial.X (Sum.inl c))) = (z c : ℂ) := by
  simp [character,realCoordinates,polynomialCharacter]

@[simp] theorem character_source_radius (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz) (i : Fin r) :
    character q₀ z hz (sourceRadius q₀ i) = (‖summands q₀ z i‖ : ℂ) := by
  simp [character,realCoordinates]

@[simp] theorem character_source_summand (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz) (i : Fin r) (q : TensorIndex d n) :
    character q₀ z hz (sourceSummand q₀ i q) = (summands q₀ z i q : ℂ) := by
  simp only [character,sourceSummand,characterFromValues_sourceHom,
    polynomialCharacter_real_summand]

@[simp] theorem character_source_radiusInverse (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz) (i : Fin r) :
    character q₀ z hz (sourceRadiusInverse q₀ i) = ((‖summands q₀ z i‖ : ℂ))⁻¹ := by
  simp [character,realCoordinates]

/-- Literal input and individually normalized output coordinates. -/
def realGraphValues (q₀ : Fin r → TensorIndex d n) (z : Parameter ℝ q₀) :
    OutputCoordinate d n r → ℝ
  | Sum.inl q => sum q₀ z q
  | Sum.inr (i,q) => summands q₀ z i q / ‖summands q₀ z i‖

/-- Evaluation of the algebraic graph coordinates is the actual real graph. -/
@[simp] theorem character_graphCoordinate (q₀ : Fin r → TensorIndex d n)
    (z : Parameter ℝ q₀) (hz) (c : OutputCoordinate d n r) :
    character q₀ z hz (graphCoordinate q₀ c) = (realGraphValues q₀ z c : ℂ) := by
  cases c with
  | inl q => simp [graphCoordinate,realGraphValues,sum]
  | inr c =>
    rcases c with ⟨i,q⟩
    simp [graphCoordinate,realGraphValues,div_eq_mul_inv]

#print axioms character
#print axioms character_graphCoordinate
#assert_trust kernel character
#assert_trust kernel character_graphCoordinate
end NLA.Proofs.TR06.GraphCharacter
