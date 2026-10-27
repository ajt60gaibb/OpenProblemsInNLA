import NLA.Proofs.RE06.SVDPartition

/-! The range-finder bound for the actual chosen SVD and actual residual
projector. All rank assumptions remain concrete internal random events. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

def headCoordinates {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (G : Matrix (Fin n) (Fin k) ℝ) :
    Matrix (Fin r) (Fin k) ℝ :=
  ((exactSVD C).V*headEmbedding n r hr).transpose*G

def tailRandomEnergy {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (G : Matrix (Fin n) (Fin k) ℝ) : ℝ :=
  squaredFrobenius (tailDiagonal C r*((exactSVD C).V.transpose*G)*
    pseudoInverse (headCoordinates C r hr G)) 0

theorem tailRandomEnergy_nonneg {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (G : Matrix (Fin n) (Fin k) ℝ) :
    0 ≤ tailRandomEnergy C r hr G := squaredFrobenius_zero_nonneg _

theorem actual_rangefinder_majorant {n k : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (G : Matrix (Fin n) (Fin k) ℝ)
    (hOmega : headCoordinates C r hr G*pseudoInverse (headCoordinates C r hr G)=1) :
    squaredFrobenius (actualRangeResidual (C*G) C) 0 ≤
      residualTailEnergy C r+tailRandomEnergy C r hr G := by
  let Q := rangeBasisMatrix (C*G)
  have hQ : Q.transpose*Q=1 := rangeBasisMatrix_gram _
  have hRange : Set.range Q.mulVec=Set.range (C*G).mulVec := rangeBasisMatrix_range _
  rw [actualRangeResidual_basis (C*G) Q hQ hRange]
  have h := weighted_rangefinder_majorant C
    ((exactSVD C).U*headEmbedding n r hr) ((exactSVD C).V*headEmbedding n r hr)
    (exactSVD C).U (exactSVD C).V (headDiagonal C r hr) (tailDiagonal C r) G Q
    (residual_svd_partition C r hr) (Pseudo.svd_U_gram C)
    (headEmbedding_isometry _ (Pseudo.svd_V_gram C) r hr) (Pseudo.svd_V_gram C)
    (residual_tail_weighted_orthogonal C r hr) hOmega hQ hRange
  simpa only [residual_tail_energy, tailRandomEnergy, headCoordinates] using h

def actualExcessMajorant {n k ell : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (r : ℕ) (hr : r ≤ n) (G : Matrix (Fin n) (Fin k) ℝ)
    (Ht : Matrix (Fin ell) (Fin n) ℝ) : ℝ :=
  tailRandomEnergy C r hr G+actualRegressionEnergy (C*G) C Ht

theorem actualExcessMajorant_nonneg {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (G : Matrix (Fin n) (Fin k) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ) :
    0 ≤ actualExcessMajorant C r hr G Ht :=
  add_nonneg (tailRandomEnergy_nonneg C r hr G) (actualRegressionEnergy_nonneg _ _ _)

/-- An all-H bound on the actual repair; only the head block rank event is
needed for the range-finder step. The excess is basis-free and nonnegative. -/
theorem actual_svd_repair_majorant {n k ell : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℕ) (hr : r ≤ n)
    (G : Matrix (Fin n) (Fin k) ℝ) (Ht : Matrix (Fin ell) (Fin n) ℝ)
    (hOmega : headCoordinates C r hr G*pseudoInverse (headCoordinates C r hr G)=1) :
    squaredFrobenius (C-(C*G)*pseudoInverse (Ht*(C*G))*(Ht*C)) 0 ≤
      residualTailEnergy C r+actualExcessMajorant C r hr G Ht := by
  rw [actual_repair_pythagoras]
  exact add_le_add_right (actual_rangefinder_majorant C r hr G hOmega) _

#assert_trust kernel tailRandomEnergy_nonneg
#assert_trust kernel actual_rangefinder_majorant
#assert_trust kernel actualExcessMajorant_nonneg
#assert_trust kernel actual_svd_repair_majorant
#print axioms actual_svd_repair_majorant
end NLA.Proofs.RE06.Repair
