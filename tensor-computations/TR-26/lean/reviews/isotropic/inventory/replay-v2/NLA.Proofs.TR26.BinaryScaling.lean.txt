import NLA.Proofs.TR26.Wronskian

/-! Scaling identities retain the fixed homogeneous degree even when the
leading affine coefficients vanish. Both projective chart endpoints are
included. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.TR26

theorem binaryEval_homogeneous_smul (k : ℕ) (P : BinaryForm ℂ)
    (hP : P.IsHomogeneous k) (a b c : ℂ) :
    binaryEval P (c*a) (c*b) = c^k * binaryEval P a b := by
  rw [binary_homogeneous_reconstruct P hP]
  simp only [binaryEvalOver,map_sum,map_mul,map_pow,MvPolynomial.eval_C,
    MvPolynomial.eval_X,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : k-i.val+i.val=k := Nat.sub_add_cancel (Nat.le_of_lt_succ i.isLt)
  simp only [mul_pow]
  calc
    _ = (c^(k-i.val)*c^i.val) *
        (binaryCoeff k P i * a^(k-i.val)*b^i.val) := by ring
    _ = _ := by rw [← pow_add,hi]

theorem binaryEval_homogeneous_zero (k : ℕ) (hk : 0 < k) (P : BinaryForm ℂ)
    (hP : P.IsHomogeneous k) : binaryEval P 0 0 = 0 := by
  simpa [zero_pow (Nat.ne_of_gt hk)] using binaryEval_homogeneous_smul k P hP 1 1 0

theorem binaryEval_affine_ratio (k : ℕ) (P : BinaryForm ℂ)
    (hP : P.IsHomogeneous k) (a b : ℂ) (ha : a ≠ 0) :
    binaryEval P a b = a^k * binaryEval P 1 (b/a) := by
  simpa [mul_div_cancel₀ _ ha] using binaryEval_homogeneous_smul k P hP 1 (b/a) a

theorem binaryEval_reverse_ratio (k : ℕ) (P : BinaryForm ℂ)
    (hP : P.IsHomogeneous k) (a b : ℂ) (hb : b ≠ 0) :
    binaryEval P a b = b^k * binaryEval P (a/b) 1 := by
  simpa [mul_div_cancel₀ _ hb] using binaryEval_homogeneous_smul k P hP (a/b) 1 b

#assert_trust kernel binaryEval_homogeneous_smul
#assert_trust kernel binaryEval_homogeneous_zero
#assert_trust kernel binaryEval_affine_ratio
#assert_trust kernel binaryEval_reverse_ratio
#print axioms binaryEval_homogeneous_smul
end NLA.Proofs.TR26
