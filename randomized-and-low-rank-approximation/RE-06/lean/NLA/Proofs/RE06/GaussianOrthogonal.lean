import NLA.Proofs.RE06.GaussianRotation

/-! Orthogonal real matrices act by genuine Euclidean isometries, and
rectangular column-isometries preserve the actual squared Frobenius energy. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Matrix
open NLA.Computation.NonadaptiveMatrixQuery
namespace NLA.Proofs.RE06

/-- Scalar squared Frobenius energy is the trace of the actual Gram matrix. -/
theorem squaredFrobenius_zero_eq_trace {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    squaredFrobenius X 0 = Matrix.trace (X.transpose * X) := by
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem squaredFrobenius_transpose_zero {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ) :
    squaredFrobenius X.transpose 0 = squaredFrobenius X 0 := by
  simp only [squaredFrobenius, Matrix.zero_apply, sub_zero, Matrix.transpose_apply]
  exact Finset.sum_comm

/-- Includes non-square orthonormal-column maps and empty dimensions. -/
theorem squaredFrobenius_left_isometry {a b c : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (hU : U.transpose * U = 1)
    (X : Matrix (Fin b) (Fin c) ℝ) :
    squaredFrobenius (U * X) 0 = squaredFrobenius X 0 := by
  rw [squaredFrobenius_zero_eq_trace, squaredFrobenius_zero_eq_trace, Matrix.transpose_mul]
  have he : X.transpose * U.transpose * (U * X) = X.transpose * (U.transpose * U) * X := by
    simp only [Matrix.mul_assoc]
  rw [he, hU, Matrix.mul_one]

theorem squaredFrobenius_right_isometry {a b c : ℕ}
    (U : Matrix (Fin a) (Fin b) ℝ) (hU : U.transpose * U = 1)
    (X : Matrix (Fin c) (Fin b) ℝ) :
    squaredFrobenius (X * U.transpose) 0 = squaredFrobenius X 0 := by
  rw [← squaredFrobenius_transpose_zero (X * U.transpose), Matrix.transpose_mul,
    Matrix.transpose_transpose, squaredFrobenius_left_isometry U hU,
    squaredFrobenius_transpose_zero]

theorem orthogonalEuclidean_inner_map (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) (x y : GaussianEuclid n) :
    inner ℝ (Matrix.toEuclideanLin U x) (Matrix.toEuclideanLin U y) = inner ℝ x y := by
  change (U *ᵥ WithLp.ofLp y) ⬝ᵥ (star (U *ᵥ WithLp.ofLp x)) =
    (WithLp.ofLp y) ⬝ᵥ (star (WithLp.ofLp x))
  simp only [star_trivial]
  rw [← Matrix.dotProduct_transpose_mulVec U (WithLp.ofLp x) (U *ᵥ WithLp.ofLp y),
    Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
  exact dotProduct_comm _ _

/-- A Gram identity constructs the genuine isometry used in Gaussian rotation. -/
def orthogonalEuclidean (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) : GaussianEuclid n ≃ₗᵢ[ℝ] GaussianEuclid n :=
  let L := (Matrix.toEuclideanLin U).isometryOfInner (orthogonalEuclidean_inner_map n U hU)
  LinearIsometryEquiv.ofSurjective L
    (LinearMap.surjective_of_injective (f := L.toLinearMap) L.injective)

theorem orthogonalEuclidean_apply (n : ℕ) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : U.transpose * U = 1) (x : GaussianEuclid n) :
    WithLp.ofLp (orthogonalEuclidean n U hU x) = U *ᵥ WithLp.ofLp x := rfl

#assert_trust kernel squaredFrobenius_zero_eq_trace
#assert_trust kernel squaredFrobenius_transpose_zero
#assert_trust kernel squaredFrobenius_left_isometry
#assert_trust kernel squaredFrobenius_right_isometry
#assert_trust kernel orthogonalEuclidean_inner_map
#assert_trust kernel orthogonalEuclidean
#assert_trust kernel orthogonalEuclidean_apply
#print axioms squaredFrobenius_zero_eq_trace
#print axioms squaredFrobenius_transpose_zero
#print axioms squaredFrobenius_left_isometry
#print axioms squaredFrobenius_right_isometry
#print axioms orthogonalEuclidean_inner_map
#print axioms orthogonalEuclidean
#print axioms orthogonalEuclidean_apply
end NLA.Proofs.RE06
