import NLA.Proofs.RA10.RidgeResolventOpNorm

/-! RA-10 selected-range Euclidean L2 operator-norm bound with the exact
source cutoff. The nuclear ideal inequality and full transfer target remain
open. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators Matrix.Norms.L2Operator

namespace NLA.Proofs.RA10

private theorem selectedSpectralMatrix_eq_diagonal {n : ℕ}
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

private theorem selectedOrthogonal_conjugation_opNorm {n : ℕ}
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

theorem matchedLeading_selectedResolvent_opNorm_le {n k : ℕ} {s : ℝ}
    (hs : 0 < s) (hk : 1 ≤ k) (hkn : k < n)
    {A Ahat : Matrix (Fin n) (Fin n) ℝ}
    {eigenvaluesA eigenvaluesAhat : Fin n → ℝ}
    {QA QAhat : Matrix (Fin n) (Fin n) ℝ}
    (hA : NLA.Statements.RA10.OrderedPSDSpectralDecomposition A eigenvaluesA QA)
    (hAhat : NLA.Statements.RA10.OrderedPSDSpectralDecomposition Ahat eigenvaluesAhat QAhat)
    (j : Fin n) (hj : j.val + 1 = k) :
    ‖selectedProjection k QAhat *
      (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
        NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
      selectedProjection k QAhat‖ ≤ 1 / (s + eigenvaluesA j) := by
  have hB0 := matchedLeading_orderedPSD (k := k) hA hAhat
  have hQTQ : QAhat.transpose * QAhat = 1 := by
    ext a b
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using hAhat.2.2.1 a b
  let w : Fin n → ℝ := fun a =>
    if a.val < k then 1 / (s + eigenvaluesA a) else 0
  have hrep :
      selectedProjection k QAhat *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
          NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        selectedProjection k QAhat =
      QAhat * Matrix.diagonal w * QAhat.transpose := by
    rw [← spectralShift_inverse hs hB0]
    rw [selectedProjection_functionMatrix hB0 (fun x => 1 / (s + x))]
    calc
      NLA.Statements.RA10.FunctionTruncation k
          (fun x => 1 / (s + x))
          (fun a : Fin n => if a.val < k then eigenvaluesA a else 0) QAhat =
          NLA.Statements.RA10.SpectralMatrix w QAhat := by
            ext i l
            simp only [NLA.Statements.RA10.FunctionTruncation,
              NLA.Statements.RA10.SpectralMatrix, Matrix.of_apply]
            apply Finset.sum_congr rfl
            intro a _
            by_cases ha : a.val < k <;> simp [w, ha]
      _ = QAhat * Matrix.diagonal w * QAhat.transpose :=
        selectedSpectralMatrix_eq_diagonal w QAhat
  have hsc : 0 < s + eigenvaluesA j := by linarith [hA.1 j]
  have hw : ‖w‖ ≤ 1 / (s + eigenvaluesA j) := by
    apply (pi_norm_le_iff_of_nonneg (le_of_lt (one_div_pos.mpr hsc))).mpr
    intro a
    by_cases ha : a.val < k
    · have haj : a ≤ j := by
        apply Fin.le_iff_val_le_val.mpr
        omega
      have hleval : eigenvaluesA j ≤ eigenvaluesA a := hA.2.1 haj
      have hsa : 0 < s + eigenvaluesA a := by linarith [hA.1 a]
      have hle : 1 / (s + eigenvaluesA a) ≤ 1 / (s + eigenvaluesA j) :=
        one_div_le_one_div_of_le hsc (by linarith)
      simp only [w, ha, ite_true]
      rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hsa)]
      exact hle
    · simp only [w, ha, ite_false, norm_zero]
      simpa using le_of_lt (one_div_pos.mpr hsc)
  calc
    ‖selectedProjection k QAhat *
        (s • (1 : Matrix (Fin n) (Fin n) ℝ) +
          NLA.Statements.RA10.FunctionTruncation k (fun t : ℝ => t) eigenvaluesA QAhat)⁻¹ *
        selectedProjection k QAhat‖ =
        ‖QAhat * Matrix.diagonal w * QAhat.transpose‖ := by rw [hrep]
    _ = ‖(Matrix.diagonal w : Matrix (Fin n) (Fin n) ℝ)‖ :=
      selectedOrthogonal_conjugation_opNorm QAhat _ hQTQ
    _ = ‖w‖ := Matrix.l2_opNorm_diagonal w
    _ ≤ 1 / (s + eigenvaluesA j) := hw

#assert_trust kernel matchedLeading_selectedResolvent_opNorm_le
#print axioms matchedLeading_selectedResolvent_opNorm_le

end NLA.Proofs.RA10
