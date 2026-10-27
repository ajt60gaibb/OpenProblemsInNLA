import NLA.Proofs.RE06.SubspaceBasis
import NLA.Proofs.RE06.RepairRegression

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

def actualProjector {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := Y*pseudoInverse Y

def actualRangeResidual {n k c : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ)
    (C : Matrix (Fin n) (Fin c) ℝ) : Matrix (Fin n) (Fin c) ℝ :=
  C-actualProjector Y*C

theorem actualProjector_transpose {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    (actualProjector Y).transpose=actualProjector Y := Pseudo.mul_pseudoinverse_transpose Y

theorem actualProjector_mul {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    actualProjector Y*Y=Y := Pseudo.mul_pseudoinverse_mul Y

theorem actualProjector_idempotent {n k : ℕ} (Y : Matrix (Fin n) (Fin k) ℝ) :
    actualProjector Y*actualProjector Y=actualProjector Y := by
  change actualProjector Y*(Y*pseudoInverse Y)=_
  rw [← Matrix.mul_assoc, actualProjector_mul]
  rfl

theorem actualProjector_basis {n k d : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (hrange : Set.range Q.mulVec=Set.range Y.mulVec) :
    actualProjector Y = Q*Q.transpose := by
  have hd : (((1 : Matrix (Fin n) (Fin n) ℝ)*Q).transpose*
      ((1 : Matrix (Fin n) (Fin n) ℝ)*Q)).det ≠ 0 := by
    simp only [Matrix.one_mul, hQ, Matrix.det_one, ne_eq, one_ne_zero, not_false_eq_true]
  have h := Pseudo.repair_orthonormal_range Y Q 1 hQ hrange hd
  simpa only [Matrix.one_mul, Pseudo.orthonormal_columns Q hQ, actualProjector] using h

theorem actualRangeResidual_basis {n k d c : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin d) ℝ)
    (hQ : Q.transpose*Q=1) (hrange : Set.range Q.mulVec=Set.range Y.mulVec)
    (C : Matrix (Fin n) (Fin c) ℝ) :
    actualRangeResidual Y C=rangeResidual Q C := by
  rw [actualRangeResidual, actualProjector_basis Y Q hQ hrange]
  simp only [rangeResidual, Matrix.mul_assoc]

theorem actualRangeResidual_orthogonal {n k c : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin n) (Fin c) ℝ) :
    (actualRangeResidual Y C).transpose*Y=0 := by
  rw [actualRangeResidual, Matrix.transpose_sub, Matrix.transpose_mul,
    actualProjector_transpose, Matrix.sub_mul, Matrix.mul_assoc,
    actualProjector_mul, sub_self]

theorem actualRangeResidual_orthogonal_factor {n k c b : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (X : Matrix (Fin k) (Fin b) ℝ) :
    (actualRangeResidual Y C).transpose*(Y*X)=0 := by
  rw [← Matrix.mul_assoc, actualRangeResidual_orthogonal, Matrix.zero_mul]

/-- This basis-free regression excess is nonnegative and globally measurable
once composed with the proved actual pseudoinverse map. -/
def actualRegressionEnergy {n k c ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ) : ℝ :=
  squaredFrobenius (actualProjector Y*C-Y*pseudoInverse (Ht*Y)*(Ht*C)) 0

theorem actualRegressionEnergy_nonneg {n k c ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ) :
    0 ≤ actualRegressionEnergy Y C Ht := squaredFrobenius_zero_nonneg _

theorem actual_repair_pythagoras {n k c ell : ℕ}
    (Y : Matrix (Fin n) (Fin k) ℝ) (C : Matrix (Fin n) (Fin c) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ) :
    squaredFrobenius (C-Y*pseudoInverse (Ht*Y)*(Ht*C)) 0 =
      squaredFrobenius (actualRangeResidual Y C) 0 + actualRegressionEnergy Y C Ht := by
  let D := actualProjector Y*C-Y*pseudoInverse (Ht*Y)*(Ht*C)
  have hz : (actualRangeResidual Y C).transpose*D=0 := by
    dsimp only [D, actualProjector]
    rw [Matrix.mul_sub]
    have h1 := actualRangeResidual_orthogonal_factor Y C (pseudoInverse Y*C)
    have h2 := actualRangeResidual_orthogonal_factor Y C (pseudoInverse (Ht*Y)*(Ht*C))
    simpa only [Matrix.mul_assoc] using sub_eq_zero.mpr (h1.trans h2.symm)
  have he : C-Y*pseudoInverse (Ht*Y)*(Ht*C) = actualRangeResidual Y C-(-D) := by
    dsimp only [actualRangeResidual,D]
    abel
  rw [he, squaredFrobenius_pythagoras _ _ (by rw [Matrix.mul_neg, hz, neg_zero])]
  congr 1
  simp only [actualRegressionEnergy, squaredFrobenius, Matrix.zero_apply,
    sub_zero, Matrix.neg_apply, neg_sq, D]

#assert_trust kernel actualProjector_transpose
#assert_trust kernel actualProjector_mul
#assert_trust kernel actualProjector_idempotent
#assert_trust kernel actualProjector_basis
#assert_trust kernel actualRangeResidual_basis
#assert_trust kernel actualRangeResidual_orthogonal
#assert_trust kernel actualRangeResidual_orthogonal_factor
#assert_trust kernel actualRegressionEnergy_nonneg
#assert_trust kernel actual_repair_pythagoras
#print axioms actual_repair_pythagoras
end NLA.Proofs.RE06.Repair
