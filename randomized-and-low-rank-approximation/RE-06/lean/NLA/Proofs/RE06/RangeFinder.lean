import NLA.Proofs.RE06.RepairProjection

set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.Proofs.RE06.Repair
open NLA.Computation.NonadaptiveMatrixQuery

theorem squaredFrobenius_row_pythagoras {a b : ℕ}
    (X Y : Matrix (Fin a) (Fin b) ℝ) (h : X * Y.transpose = 0) :
    squaredFrobenius (X-Y) 0 = squaredFrobenius X 0 + squaredFrobenius Y 0 := by
  rw [← squaredFrobenius_transpose_zero (X-Y), Matrix.transpose_sub,
    squaredFrobenius_pythagoras X.transpose Y.transpose
      (by simpa only [Matrix.transpose_transpose] using h),
    squaredFrobenius_transpose_zero, squaredFrobenius_transpose_zero]

/-- The source range-finder identity uses no inverse of a singular value. -/
theorem rangefinder_error {n r t k : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (U1 V1 : Matrix (Fin n) (Fin r) ℝ)
    (U2 V2 : Matrix (Fin n) (Fin t) ℝ)
    (S1 : Matrix (Fin r) (Fin r) ℝ) (S2 : Matrix (Fin t) (Fin t) ℝ)
    (G : Matrix (Fin n) (Fin k) ℝ)
    (hC : C = U1*S1*V1.transpose + U2*S2*V2.transpose)
    (hU2 : U2.transpose*U2=1) (hV1 : V1.transpose*V1=1)
    (hV2 : V2.transpose*V2=1) (hV21 : V2.transpose*V1=0)
    (hOmega : (V1.transpose*G)*pseudoInverse (V1.transpose*G)=1) :
    squaredFrobenius (C-C*G*pseudoInverse (V1.transpose*G)*V1.transpose) 0 =
      squaredFrobenius S2 0 +
      squaredFrobenius (S2*(V2.transpose*G)*pseudoInverse (V1.transpose*G)) 0 := by
  have ha : C*G*pseudoInverse (V1.transpose*G)*V1.transpose =
      U1*S1*V1.transpose + U2*S2*(V2.transpose*G)*
        pseudoInverse (V1.transpose*G)*V1.transpose := by
    calc
      _ = (U1*S1)*((V1.transpose*G)*pseudoInverse (V1.transpose*G))*V1.transpose +
          U2*S2*(V2.transpose*G)*pseudoInverse (V1.transpose*G)*V1.transpose := by
        rw [hC]
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = _ := by rw [hOmega, Matrix.mul_one]
  have he : C-C*G*pseudoInverse (V1.transpose*G)*V1.transpose =
      U2*(S2*V2.transpose-S2*(V2.transpose*G)*
        pseudoInverse (V1.transpose*G)*V1.transpose) := by
    rw [ha, hC]
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    abel
  rw [he, squaredFrobenius_left_isometry U2 hU2]
  have ho : (S2*V2.transpose) *
      (S2*(V2.transpose*G)*pseudoInverse (V1.transpose*G)*V1.transpose).transpose = 0 := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc V2.transpose V1 _, hV21, Matrix.zero_mul, Matrix.mul_zero]
  rw [squaredFrobenius_row_pythagoras _ _ ho,
    squaredFrobenius_right_isometry V2 hV2,
    squaredFrobenius_right_isometry V1 hV1]

theorem rangefinder_majorant {n r t k d : ℕ}
    (C : Matrix (Fin n) (Fin n) ℝ)
    (U1 V1 : Matrix (Fin n) (Fin r) ℝ)
    (U2 V2 : Matrix (Fin n) (Fin t) ℝ)
    (S1 : Matrix (Fin r) (Fin r) ℝ) (S2 : Matrix (Fin t) (Fin t) ℝ)
    (G : Matrix (Fin n) (Fin k) ℝ) (Q : Matrix (Fin n) (Fin d) ℝ)
    (hC : C = U1*S1*V1.transpose + U2*S2*V2.transpose)
    (hU2 : U2.transpose*U2=1) (hV1 : V1.transpose*V1=1)
    (hV2 : V2.transpose*V2=1) (hV21 : V2.transpose*V1=0)
    (hOmega : (V1.transpose*G)*pseudoInverse (V1.transpose*G)=1)
    (hQ : Q.transpose*Q=1) (hrange : Set.range Q.mulVec = Set.range (C*G).mulVec) :
    squaredFrobenius (rangeResidual Q C) 0 ≤ squaredFrobenius S2 0 +
      squaredFrobenius (S2*(V2.transpose*G)*pseudoInverse (V1.transpose*G)) 0 := by
  rw [← rangefinder_error C U1 V1 U2 V2 S1 S2 G hC hU2 hV1 hV2 hV21 hOmega]
  apply rangeResidual_le_range_approximation Q hQ C
  rw [hrange]
  apply (Pseudo.range_subset_iff_matrix_factor _ _).mpr
  exact ⟨pseudoInverse (V1.transpose*G)*V1.transpose, by simp only [Matrix.mul_assoc]⟩

#assert_trust kernel squaredFrobenius_row_pythagoras
#assert_trust kernel rangefinder_error
#assert_trust kernel rangefinder_majorant
#print axioms rangefinder_majorant
end NLA.Proofs.RE06.Repair
