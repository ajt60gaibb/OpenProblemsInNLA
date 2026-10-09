import NLA.TR07.FiniteVector
import NLA.TR07.SpectralFilter
import Mathlib.LinearAlgebra.Matrix.Trace

/-! Covariances of finite Euclidean laws and their linear transformations. -/
noncomputable section
open scoped BigOperators
open Matrix
attribute [local instance] Classical.propDecidable
namespace NLA.TR07

variable {α ι κ : Type*} [Fintype α] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

def covariance (p : Law α) (u : α → EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  ∑ a, p.wt a • vecMulVec (u a) (u a)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem covariance_apply (p : Law α) (u : α → EuclideanSpace ℝ ι) (i j : ι) :
    covariance p u i j = p.expect (fun a => u a i * u a j) := by
  simp only [covariance, Law.expect, Matrix.sum_apply, Matrix.smul_apply,
    vecMulVec_apply, smul_eq_mul]

omit [DecidableEq ι] in
theorem covariance_psd (p : Law α) (u : α → EuclideanSpace ℝ ι) :
    (covariance p u).PosSemidef := by
  apply posSemidef_sum
  intro a _
  have hp : (vecMulVec (u a) (u a)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (⇑(u a))
  exact hp.smul (p.nonneg a)

omit [DecidableEq ι] in
theorem covariance_trace (p : Law α) (u : α → EuclideanSpace ℝ ι) :
    (covariance p u).trace = p.expect (fun a => ‖u a‖ ^ 2) := by
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  simp only [covariance, trace_sum, trace_smul, trace_vecMulVec, smul_eq_mul,
    Law.expect, dotProduct, pow_two]

omit [Fintype κ] [DecidableEq κ] in
theorem covariance_transform (p : Law α) (u : α → EuclideanSpace ℝ ι)
    (B : Matrix κ ι ℝ) :
    covariance p (fun a => B.toEuclideanLin (u a)) = B * covariance p u * Bᵀ := by
  simp only [covariance, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul, vecMul_transpose, Matrix.toLpLin_apply, WithLp.ofLp_toLp]

omit [DecidableEq ι] in
theorem covariance_quadratic (p : Law α) (u : α → EuclideanSpace ℝ ι) (x : ι → ℝ) :
    x ⬝ᵥ (covariance p u *ᵥ x) = p.expect (fun a => ((⇑(u a)) ⬝ᵥ x) ^ 2) := by
  simp only [covariance, sum_mulVec, smul_mulVec,
    vecMulVec_mulVec, Law.expect, dotProduct_comm x, pow_two]
  simp [sum_dotProduct, smul_dotProduct, smul_eq_mul]

/-- Trace against a nonnegative diagonal preserves an upper positive-semidefinite bound. -/
theorem weighted_trace_le {A : Matrix ι ι ℝ} {c : ℝ}
    (h : (c • (1 : Matrix ι ι ℝ) - A).PosSemidef)
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (diagonal d * A).trace ≤ c * ∑ i, d i := by
  have hi (i : ι) : A i i ≤ c := by
    have := h.diag_nonneg (i := i)
    simpa only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, sub_nonneg] using this
  change (∑ i, (diagonal d * A) i i) ≤ _
  simp only [diagonal_mul]
  calc
    ∑ i, d i * A i i ≤ ∑ i, d i * c :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi i) (hd i)
    _ = c * ∑ i, d i := by rw [← Finset.sum_mul, mul_comm]

end NLA.TR07
