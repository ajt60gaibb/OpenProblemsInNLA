/-
Exact Euclidean matrix singular values and spectral pseudoinverse. The source
conventions and signatures were independently approved before implementation
in reviews/spectral-stacking-specification.md. No stochastic estimate is assumed.
-/
import Mathlib
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Matrix Module
open scoped Matrix.Norms.L2Operator
namespace NLA.IE06.Spectral

variable {r c : Type*} [Fintype r] [Fintype c] [DecidableEq r] [DecidableEq c]

/-- The actual Euclidean linear map represented by the matrix. -/
def euclideanMap (A : Matrix r c ℝ) : EuclideanSpace ℝ c →ₗ[ℝ] EuclideanSpace ℝ r :=
  Matrix.toEuclideanLin A

def opNorm (A : Matrix r c ℝ) : ℝ := ‖(euclideanMap A).toContinuousLinearMap‖

/-- Descending, zero-based, rank-zero-extended singular values. Source index
ell ≥ 1 is represented by singularValue A (ell-1). -/
def singularValue (A : Matrix r c ℝ) (i : ℕ) : ℝ := (euclideanMap A).singularValues i

/-- Genuine spectral Moore–Penrose construction, including singular matrices.
On the finite Gram spectrum, scalar inverse sends the zero eigenvalue to zero. -/
def pinv (A : Matrix r c ℝ) : Matrix c r ℝ :=
  Aᴴ * cfc (fun t : ℝ => t⁻¹) (A * Aᴴ)

omit [DecidableEq r] in
theorem opNorm_eq_l2 (A : Matrix r c ℝ) : opNorm A = ‖A‖ := rfl

omit [DecidableEq r] in
theorem opNorm_nonneg (A : Matrix r c ℝ) : 0 ≤ opNorm A := norm_nonneg _

omit [DecidableEq r] in
theorem singularValue_nonneg (A : Matrix r c ℝ) (i : ℕ) : 0 ≤ singularValue A i :=
  (euclideanMap A).singularValues_nonneg i

omit [DecidableEq r] in
theorem singularValue_antitone (A : Matrix r c ℝ) : Antitone (singularValue A) :=
  (euclideanMap A).singularValues_antitone

omit [DecidableEq r] in
theorem singularValue_pos_iff (A : Matrix r c ℝ) (i : ℕ) :
    0 < singularValue A i ↔ i < finrank ℝ (euclideanMap A).range :=
  (euclideanMap A).singularValues_pos_iff_lt_finrank_range

omit [DecidableEq r] in
theorem singularValue_eq_zero_iff (A : Matrix r c ℝ) (i : ℕ) :
    singularValue A i = 0 ↔ finrank ℝ (euclideanMap A).range ≤ i :=
  (euclideanMap A).singularValues_eq_zero_iff_le_finrank_range

omit [DecidableEq c] in
theorem pinv_spectral_formula (A : Matrix r c ℝ) :
    let h := Matrix.isHermitian_mul_conjTranspose_self A
    pinv A = Aᴴ * ((h.eigenvectorUnitary : Matrix r r ℝ) *
      Matrix.diagonal (fun i => (h.eigenvalues i)⁻¹) *
      (h.eigenvectorUnitary : Matrix r r ℝ)ᴴ) := by
  dsimp only
  rw [pinv, (Matrix.isHermitian_mul_conjTranspose_self A).cfc_eq]
  rfl

omit [DecidableEq c] in
theorem pinv_eq_gram_inverse (A : Matrix r c ℝ) (h : IsUnit (A * Aᴴ)) :
    pinv A = Aᴴ * (A * Aᴴ)⁻¹ := by
  rw [pinv, cfc_ringInverse_id (A * Aᴴ) h (Matrix.isHermitian_mul_conjTranspose_self A).isSelfAdjoint,
    ← Matrix.nonsing_inv_eq_ringInverse]

omit [DecidableEq c] in
theorem mul_pinv_eq_one (A : Matrix r c ℝ) (h : IsUnit (A * Aᴴ)) :
    A * pinv A = 1 := by
  rw [pinv_eq_gram_inverse A h, ← Matrix.mul_assoc]
  exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h)

omit [DecidableEq c] in
theorem pinv_gram (A : Matrix r c ℝ) (h : IsUnit (A * Aᴴ)) :
    (pinv A)ᴴ * pinv A = (A * Aᴴ)⁻¹ := by
  have hherm : ((A * Aᴴ)⁻¹).IsHermitian :=
    (Matrix.isHermitian_mul_conjTranspose_self A).inv
  rw [pinv_eq_gram_inverse A h, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hherm.eq]
  calc
    (A * Aᴴ)⁻¹ * A * (Aᴴ * (A * Aᴴ)⁻¹) =
        (A * Aᴴ)⁻¹ * ((A * Aᴴ) * (A * Aᴴ)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp h), Matrix.mul_one]

omit [DecidableEq c] in
theorem opNorm_pinv_sq_eq_gram_inverse (A : Matrix r c ℝ) (h : IsUnit (A * Aᴴ)) :
    opNorm (pinv A) ^ 2 = opNorm ((A * Aᴴ)⁻¹) := by
  simp only [opNorm_eq_l2]
  rw [pow_two, ← Matrix.l2_opNorm_conjTranspose_mul_self, pinv_gram A h]

omit [DecidableEq c] in
theorem pinv_eq_gram_inverse_of_posDef (A : Matrix r c ℝ) (h : (A * Aᴴ).PosDef) :
    pinv A = Aᴴ * (A * Aᴴ)⁻¹ := pinv_eq_gram_inverse A h.isUnit

omit [DecidableEq c] in
theorem opNorm_pinv_sq_eq_gram_inverse_of_posDef (A : Matrix r c ℝ)
    (h : (A * Aᴴ).PosDef) :
    opNorm (pinv A) ^ 2 = opNorm ((A * Aᴴ)⁻¹) :=
  opNorm_pinv_sq_eq_gram_inverse A h.isUnit

/-- Full Euclidean row rank makes the row Gram matrix strictly positive definite. -/
theorem gram_posDef_of_surjective (A : Matrix r c ℝ)
    (h : Function.Surjective (euclideanMap A)) : (A * Aᴴ).PosDef := by
  have hi : Function.Injective (euclideanMap A).adjoint := by
    rw [← LinearMap.ker_eq_bot, ← LinearMap.orthogonal_range,
      LinearMap.range_eq_top.mpr h, Submodule.top_orthogonal_eq_bot]
  have hmul : Function.Injective (Aᴴ).mulVec := by
    intro x y hxy
    have he : (euclideanMap A).adjoint (WithLp.toLp 2 x) =
        (euclideanMap A).adjoint (WithLp.toLp 2 y) := by
      simp only [euclideanMap, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
      change WithLp.toLp 2 (Aᴴ *ᵥ x) = WithLp.toLp 2 (Aᴴ *ᵥ y)
      rw [hxy]
    exact congrArg WithLp.ofLp (hi he)
  simpa using Matrix.PosDef.conjTranspose_mul_self (Aᴴ) hmul

end NLA.IE06.Spectral

#assert_trust kernel NLA.IE06.Spectral.euclideanMap
#print axioms NLA.IE06.Spectral.euclideanMap
#assert_trust kernel NLA.IE06.Spectral.opNorm
#print axioms NLA.IE06.Spectral.opNorm
#assert_trust kernel NLA.IE06.Spectral.singularValue
#print axioms NLA.IE06.Spectral.singularValue
#assert_trust kernel NLA.IE06.Spectral.pinv
#print axioms NLA.IE06.Spectral.pinv
#assert_trust kernel NLA.IE06.Spectral.opNorm_eq_l2
#print axioms NLA.IE06.Spectral.opNorm_eq_l2
#assert_trust kernel NLA.IE06.Spectral.opNorm_nonneg
#print axioms NLA.IE06.Spectral.opNorm_nonneg
#assert_trust kernel NLA.IE06.Spectral.singularValue_nonneg
#print axioms NLA.IE06.Spectral.singularValue_nonneg
#assert_trust kernel NLA.IE06.Spectral.singularValue_antitone
#print axioms NLA.IE06.Spectral.singularValue_antitone
#assert_trust kernel NLA.IE06.Spectral.singularValue_pos_iff
#print axioms NLA.IE06.Spectral.singularValue_pos_iff
#assert_trust kernel NLA.IE06.Spectral.singularValue_eq_zero_iff
#print axioms NLA.IE06.Spectral.singularValue_eq_zero_iff
#assert_trust kernel NLA.IE06.Spectral.pinv_spectral_formula
#print axioms NLA.IE06.Spectral.pinv_spectral_formula
#assert_trust kernel NLA.IE06.Spectral.pinv_eq_gram_inverse
#print axioms NLA.IE06.Spectral.pinv_eq_gram_inverse
#assert_trust kernel NLA.IE06.Spectral.mul_pinv_eq_one
#print axioms NLA.IE06.Spectral.mul_pinv_eq_one
#assert_trust kernel NLA.IE06.Spectral.pinv_gram
#print axioms NLA.IE06.Spectral.pinv_gram
#assert_trust kernel NLA.IE06.Spectral.opNorm_pinv_sq_eq_gram_inverse
#print axioms NLA.IE06.Spectral.opNorm_pinv_sq_eq_gram_inverse
#assert_trust kernel NLA.IE06.Spectral.pinv_eq_gram_inverse_of_posDef
#print axioms NLA.IE06.Spectral.pinv_eq_gram_inverse_of_posDef
#assert_trust kernel NLA.IE06.Spectral.opNorm_pinv_sq_eq_gram_inverse_of_posDef
#print axioms NLA.IE06.Spectral.opNorm_pinv_sq_eq_gram_inverse_of_posDef
#assert_trust kernel NLA.IE06.Spectral.gram_posDef_of_surjective
#print axioms NLA.IE06.Spectral.gram_posDef_of_surjective
