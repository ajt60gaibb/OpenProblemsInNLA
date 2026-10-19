import NLA.Proofs.PF05.ContactQuartic

/-! The affine alternative polynomial detects the full homogeneous rank-one conic. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 CoordinateActions Polynomial
noncomputable section

theorem alternativePolynomial_coeff_four (L : M3) :
    (alternativePolynomial L).coeff 4 = L 1 0 * L 1 1 - (L 1 2)^2 := by
  unfold alternativePolynomial
  simp only [Polynomial.coeff_sub, pow_two, Polynomial.coeff_mul]
  simp [Finset.Nat.sum_antidiagonal_succ, coordinateQuadratic, Polynomial.coeff_X]

/-- Zero affine quartic also forces the image of the missing projective point
at infinity to be singular; no contact direction is discarded. -/
theorem alternativePolynomial_zero_outer (L : M3)
    (hzero : alternativePolynomial L = 0) (v : Fin 2 → ℝ) :
    (primal L (Matrix.vecMulVec v v)).det = 0 := by
  have hfour : L 1 0 * L 1 1 - (L 1 2)^2 = 0 := by
    rw [← alternativePolynomial_coeff_four, hzero]
    simp
  by_cases hz : v 0 = 0
  · calc
      _ = (v 1)^4 * (L 1 0 * L 1 1 - (L 1 2)^2) := by
        simp [primal, decodeLeft, leftVector, Matrix.vecMulVec_apply, Matrix.vecMul,
          dotProduct, Fin.sum_univ_three, Matrix.det_fin_two, hz]
        ring
      _ = 0 := by rw [hfour]; ring
  · have heval : (primal L (chartOuter (v 1 / v 0))).det = 0 := by
      rw [← alternativePolynomial_eval, hzero]
      simp
    have houter : Matrix.vecMulVec v v = (v 0)^2 • chartOuter (v 1 / v 0) := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.vecMulVec_apply, chartOuter, Matrix.smul_apply, smul_eq_mul] <;>
        field_simp
    rw [houter, primal_smul_input]
    simp [heval]

#assert_trust kernel alternativePolynomial_coeff_four
#assert_trust kernel alternativePolynomial_zero_outer
#print axioms alternativePolynomial_zero_outer
end
end NLA.Proofs.PF05
