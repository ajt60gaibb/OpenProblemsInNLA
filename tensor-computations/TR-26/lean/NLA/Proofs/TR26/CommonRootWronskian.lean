import NLA.Proofs.TR26.Wronskian

/-! A common root of two equal-degree binary forms is a double projective root
of their homogeneous Jacobian. The proof uses genuine polynomial derivatives
and Euler identities, with no chosen incidence equations. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace NLA.Proofs.TR26

theorem binary_euler_eval_one {m : ℕ} (P : BinaryForm ℂ) (hP : P.IsHomogeneous m) (r : ℂ) :
    binaryEval (pderiv 0 P) 1 r + r * binaryEval (pderiv 1 P) 1 r =
      (m : ℂ) * binaryEval P 1 r := by
  have h := congrArg (MvPolynomial.eval ![(1 : ℂ), r]) hP.sum_X_mul_pderiv
  simp only [map_add, map_mul, eval_X, nsmul_eq_mul, map_natCast, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, one_mul] at h
  exact h

theorem binary_mixed_partials_comm (P : BinaryForm ℂ) :
    pderiv 1 (pderiv 0 P) = pderiv 0 (pderiv 1 P) := by
  ext e
  simp [coeff_pderiv, Finsupp.add_apply,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]

def binaryJacobian (P Q : BinaryForm ℂ) : BinaryForm ℂ :=
  pderiv 1 P * pderiv 0 Q - pderiv 0 P * pderiv 1 Q

theorem binaryJacobian_homogeneous {m : ℕ} (P Q : BinaryForm ℂ)
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous m) :
    (binaryJacobian P Q).IsHomogeneous (2 * m - 2) := by
  have h := ((hP.pderiv (i := 1)).mul (hQ.pderiv (i := 0))).sub
    ((hP.pderiv (i := 0)).mul (hQ.pderiv (i := 1)))
  simpa only [binaryJacobian, show m - 1 + (m - 1) = 2 * m - 2 by omega] using h

theorem binaryJacobian_double_root_of_common_root {m : ℕ} (P Q : BinaryForm ℂ)
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous m) (r : ℂ)
    (hPr : binaryEval P 1 r = 0) (hQr : binaryEval Q 1 r = 0) :
    binaryEval (pderiv 0 (binaryJacobian P Q)) 1 r = 0 ∧
      binaryEval (pderiv 1 (binaryJacobian P Q)) 1 r = 0 := by
  have heP := binary_euler_eval_one P hP r
  have heQ := binary_euler_eval_one Q hQ r
  rw [hPr, mul_zero] at heP
  rw [hQr, mul_zero] at heQ
  have hPa : binaryEval (pderiv 0 P) 1 r = -r * binaryEval (pderiv 1 P) 1 r := by
    linear_combination heP
  have hQa : binaryEval (pderiv 0 Q) 1 r = -r * binaryEval (pderiv 1 Q) 1 r := by
    linear_combination heQ
  have hePb := binary_euler_eval_one (pderiv 1 P) (hP.pderiv (i := 1)) r
  have heQb := binary_euler_eval_one (pderiv 1 Q) (hQ.pderiv (i := 1)) r
  have hPab : binaryEval (pderiv 0 (pderiv 1 P)) 1 r =
      (m - 1 : ℕ) * binaryEval (pderiv 1 P) 1 r -
        r * binaryEval (pderiv 1 (pderiv 1 P)) 1 r := by
    linear_combination hePb
  have hQab : binaryEval (pderiv 0 (pderiv 1 Q)) 1 r =
      (m - 1 : ℕ) * binaryEval (pderiv 1 Q) 1 r -
        r * binaryEval (pderiv 1 (pderiv 1 Q)) 1 r := by
    linear_combination heQb
  have hJ : binaryEval (binaryJacobian P Q) 1 r = 0 := by
    simp only [binaryJacobian, binaryEvalOver, map_sub, map_mul]
    change binaryEval (pderiv 1 P) 1 r * binaryEval (pderiv 0 Q) 1 r -
      binaryEval (pderiv 0 P) 1 r * binaryEval (pderiv 1 Q) 1 r = 0
    rw [hPa, hQa]
    ring
  have hJb : binaryEval (pderiv 1 (binaryJacobian P Q)) 1 r = 0 := by
    simp only [binaryJacobian, map_sub, pderiv_mul, binary_mixed_partials_comm,
      binaryEvalOver, map_add, map_mul]
    change (binaryEval (pderiv 1 (pderiv 1 P)) 1 r * binaryEval (pderiv 0 Q) 1 r +
      binaryEval (pderiv 1 P) 1 r * binaryEval (pderiv 0 (pderiv 1 Q)) 1 r) -
      (binaryEval (pderiv 0 (pderiv 1 P)) 1 r * binaryEval (pderiv 1 Q) 1 r +
      binaryEval (pderiv 0 P) 1 r * binaryEval (pderiv 1 (pderiv 1 Q)) 1 r) = 0
    rw [hPa, hQa, hPab, hQab]
    ring
  have hJa := binary_euler_eval_one (binaryJacobian P Q) (binaryJacobian_homogeneous P Q hP hQ) r
  rw [hJ, hJb, mul_zero, add_zero, mul_zero] at hJa
  exact ⟨hJa, hJb⟩

#assert_trust kernel binary_euler_eval_one
#assert_trust kernel binary_mixed_partials_comm
#assert_trust kernel binaryJacobian_double_root_of_common_root
#print axioms binaryJacobian_double_root_of_common_root
end NLA.Proofs.TR26
