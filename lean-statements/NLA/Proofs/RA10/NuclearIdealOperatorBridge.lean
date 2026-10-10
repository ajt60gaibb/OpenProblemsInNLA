import NLA.Statements.RA10
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! RA-10 exact matrix/Euclidean-operator semantics for the frozen sum of
singular values and the scoped L2 operator norm. Nuclear ideal inequalities
and Equation (14)'s numerical estimate remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

theorem toEuclideanLin_mul_exact {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (X * Y) =
      (Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y) := by
  have h := map_mul (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) X Y
  have h' := congrArg
    (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) h
  change Matrix.toEuclideanLin (X * Y) =
    (Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y) at h'
  exact h'

theorem toEuclideanLin_smul_exact {n : ℕ} (r : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toEuclideanLin (r • X) = r • Matrix.toEuclideanLin X := by
  exact map_smul Matrix.toEuclideanLin r X

theorem nuclearNorm_mul_as_operator_comp {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.NuclearNorm (X * Y) =
      ∑ i : Fin n,
        ((Matrix.toEuclideanLin X).comp (Matrix.toEuclideanLin Y)).singularValues i.val := by
  rw [NLA.Statements.RA10.NuclearNorm, toEuclideanLin_mul_exact]

theorem matrix_l2_opNorm_eq_operator_norm {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) :
    ‖X‖ = ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) X‖ := by
  exact Matrix.cstar_norm_def X

#assert_trust kernel toEuclideanLin_mul_exact
#assert_trust kernel toEuclideanLin_smul_exact
#assert_trust kernel nuclearNorm_mul_as_operator_comp
#assert_trust kernel matrix_l2_opNorm_eq_operator_norm
#print axioms nuclearNorm_mul_as_operator_comp

end NLA.Proofs.RA10
