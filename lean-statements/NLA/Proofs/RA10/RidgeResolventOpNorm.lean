import NLA.Proofs.RA10.RidgeResolventLoewnerSelected
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! RA-10 Euclidean L2 operator-norm bounds for ridge resolvents. This is
distinct from the frozen sum-of-singular-values nuclear norm. The nuclear
ideal inequality and full RA-10 transfer target remain open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

private theorem spectralMatrix_eq_diagonal {n : ℕ}
    (w : Fin n → ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) :
    NLA.Statements.RA10.SpectralMatrix w Q =
      Q * Matrix.diagonal w * Q.transpose := by
  ext i j
  simp only [NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem orthogonal_conjugation_opNorm {n : ℕ}
    (Q D : Matrix (Fin n) (Fin n) ℝ)
    (hQTQ : Q.transpose * Q = 1) :
    ‖Q * D * Q.transpose‖ = ‖D‖ := by
  have hQQT : Q * Q.transpose = 1 := mul_eq_one_comm.mp hQTQ
  have hunitQ : Q ∈ Matrix.unitaryGroup (Fin n) ℝ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using hQTQ
  have hunitQT : Q.transpose ∈ Matrix.unitaryGroup (Fin n) ℝ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    simpa only [Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using hQQT
  calc
    ‖Q * D * Q.transpose‖ = ‖Q * D‖ :=
      CStarRing.norm_mul_mem_unitary (Q * D) hunitQT
    _ = ‖D‖ := CStarRing.norm_mem_unitary_mul D hunitQ

theorem spectralShift_resolvent_opNorm_le {n : ℕ} {s : ℝ}
    (hs : 0 < s)
    {C : Matrix (Fin n) (Fin n) ℝ} {eigenvaluesC : Fin n → ℝ}
    {QC : Matrix (Fin n) (Fin n) ℝ}
    (hC : NLA.Statements.RA10.OrderedPSDSpectralDecomposition C eigenvaluesC QC) :
    ‖(s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹‖ ≤ 1 / s := by
  have hQTQ : QC.transpose * QC = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hC.2.2.1 a b
  let w : Fin n → ℝ := fun a => 1 / (s + eigenvaluesC a)
  have hrep : (s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹ =
      QC * Matrix.diagonal w * QC.transpose := by
    rw [← spectralShift_inverse hs hC]
    exact spectralMatrix_eq_diagonal w QC
  have hw : ‖w‖ ≤ 1 / s := by
    apply (pi_norm_le_iff_of_nonneg (le_of_lt (one_div_pos.mpr hs))).mpr
    intro a
    have hpos : 0 < s + eigenvaluesC a := by linarith [hC.1 a]
    have hle : 1 / (s + eigenvaluesC a) ≤ 1 / s := by
      exact one_div_le_one_div_of_le hs (by linarith [hC.1 a])
    change ‖(1 : ℝ) / (s + eigenvaluesC a)‖ ≤ 1 / s
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hpos)]
    exact hle
  calc
    ‖(s • (1 : Matrix (Fin n) (Fin n) ℝ) + C)⁻¹‖ =
        ‖QC * Matrix.diagonal w * QC.transpose‖ := by rw [hrep]
    _ = ‖(Matrix.diagonal w : Matrix (Fin n) (Fin n) ℝ)‖ :=
      orthogonal_conjugation_opNorm QC _ hQTQ
    _ = ‖w‖ := Matrix.l2_opNorm_diagonal w
    _ ≤ 1 / s := hw

#assert_trust kernel spectralShift_resolvent_opNorm_le
#print axioms spectralShift_resolvent_opNorm_le

end NLA.Proofs.RA10
