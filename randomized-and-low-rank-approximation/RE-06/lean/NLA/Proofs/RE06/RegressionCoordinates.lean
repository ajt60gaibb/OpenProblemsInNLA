import NLA.Proofs.RE06.GaussianFixedRotation
import NLA.Proofs.RE06.TailPartition
import NLA.Proofs.RE06.GaussianRowSplit

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open scoped BigOperators
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem gaussianHeadEntries_matrix (n d q : ℕ) (hd : d ≤ n)
    (x : Fin n × Fin q → ℝ) :
    Matrix.of (fun i j => gaussianHeadEntries n d q hd x (i,j)) =
      (headEmbedding n d hd).transpose*Matrix.of (fun i j => x (i,j)) := by
  ext i j
  simp [Matrix.mul_apply, headEmbedding, gaussianHeadEntries]

theorem gaussianTailEntries_matrix (n d q : ℕ) (hd : d ≤ n)
    (x : Fin n × Fin q → ℝ) :
    Matrix.of (fun i j => gaussianTailEntries n d q hd x (i,j)) =
      (tailEmbedding n d hd).transpose*Matrix.of (fun i j => x (i,j)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, tailEmbedding,
    gaussianTailEntries, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  rfl

def tailCoefficients {n c : ℕ} (O : Matrix (Fin n) (Fin n) ℝ)
    (d : ℕ) (hd : d ≤ n) (R : Matrix (Fin n) (Fin c) ℝ) :
    Matrix (Fin (n-d)) (Fin c) ℝ :=
  (tailEmbedding n d hd).transpose*(O.transpose*R)

theorem orthogonal_tail_factor {n d c : ℕ}
    (O : Matrix (Fin n) (Fin n) ℝ) (hd : d ≤ n)
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : O*headEmbedding n d hd=Q)
    (R : Matrix (Fin n) (Fin c) ℝ) (hR : Q.transpose*R=0) :
    O.transpose*R=tailEmbedding n d hd*tailCoefficients O d hd R := by
  have hz : (headEmbedding n d hd).transpose*(O.transpose*R)=0 := by
    rw [← Matrix.mul_assoc, ← Matrix.transpose_mul, hQ, hR]
  calc
    _ = (headEmbedding n d hd*(headEmbedding n d hd).transpose+
          tailEmbedding n d hd*(tailEmbedding n d hd).transpose)*(O.transpose*R) := by
      rw [head_tail_projectors, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.add_mul, Matrix.mul_assoc, hz, Matrix.mul_zero, zero_add,
        tailCoefficients]

theorem tailCoefficients_energy {n d c : ℕ}
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O*O.transpose=1) (hd : d ≤ n)
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : O*headEmbedding n d hd=Q)
    (R : Matrix (Fin n) (Fin c) ℝ) (hR : Q.transpose*R=0) :
    squaredFrobenius (tailCoefficients O d hd R) 0=squaredFrobenius R 0 := by
  calc
    _ = squaredFrobenius (O.transpose*R) 0 := by
      rw [orthogonal_tail_factor O hd Q hQ R hR,
        squaredFrobenius_left_isometry _ (tailEmbedding_gram n d hd)]
    _ = _ := squaredFrobenius_left_isometry O.transpose (by
      simpa only [Matrix.transpose_transpose] using hO) R

theorem regression_head_coordinates {n d ell : ℕ}
    (O : Matrix (Fin n) (Fin n) ℝ) (hd : d ≤ n)
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : O*headEmbedding n d hd=Q)
    (x : Fin n × Fin ell → ℝ) :
    (Matrix.of (fun i j => gaussianHeadEntries n d ell hd (rotateEntries O ell x) (i,j))).transpose =
      (Matrix.of (fun i j => x (i,j))).transpose*Q := by
  rw [gaussianHeadEntries_matrix]
  change ((headEmbedding n d hd).transpose*(O.transpose*Matrix.of (fun i j => x (i,j)))).transpose=_
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose, Matrix.mul_assoc, hQ]

theorem regression_tail_coordinates {n d c ell : ℕ}
    (O : Matrix (Fin n) (Fin n) ℝ) (hO : O*O.transpose=1) (hd : d ≤ n)
    (Q : Matrix (Fin n) (Fin d) ℝ) (hQ : O*headEmbedding n d hd=Q)
    (R : Matrix (Fin n) (Fin c) ℝ) (hR : Q.transpose*R=0)
    (x : Fin n × Fin ell → ℝ) :
    (Matrix.of (fun i j => x (i,j))).transpose*R =
      (Matrix.of (fun i j => gaussianTailEntries n d ell hd (rotateEntries O ell x) (i,j))).transpose*
        tailCoefficients O d hd R := by
  rw [gaussianTailEntries_matrix]
  change (Matrix.of (fun i j => x (i,j))).transpose*R =
    ((tailEmbedding n d hd).transpose*(O.transpose*Matrix.of (fun i j => x (i,j)))).transpose*
      tailCoefficients O d hd R
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.transpose_transpose]
  have hf := orthogonal_tail_factor O hd Q hQ R hR
  calc
    _ = (Matrix.of (fun i j => x (i,j))).transpose*O*(O.transpose*R) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc O O.transpose R, hO, Matrix.one_mul]
    _ = _ := by rw [hf]; simp only [Matrix.mul_assoc]

#assert_trust kernel gaussianHeadEntries_matrix
#assert_trust kernel gaussianTailEntries_matrix
#assert_trust kernel orthogonal_tail_factor
#assert_trust kernel tailCoefficients_energy
#assert_trust kernel regression_head_coordinates
#assert_trust kernel regression_tail_coordinates
#print axioms regression_tail_coordinates
end NLA.Proofs.RE06.Repair
