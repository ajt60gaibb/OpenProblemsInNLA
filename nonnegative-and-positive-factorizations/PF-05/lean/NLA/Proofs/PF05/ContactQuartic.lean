import NLA.Proofs.PF05.CoordinateActions
import NLA.Proofs.PF05.PSDLine
import NLA.Proofs.PF05.PolynomialStrictification

/-! Actual degree-four contact polynomials in the retained weighted coordinates. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.Proofs.PF05
open NLA.Statements.PF05 Polynomial
open CoordinateActions
noncomputable section

/-- The affine rank-one chart and its trace-orthogonal dual chart. -/
def chartOuter (t : ℝ) : M2 := !![1,t;t,t^2]
def chartDual (t : ℝ) : M2 := !![t^2,-t;-t,1]

def coordinateQuadratic (a b c : ℝ) : ℝ[X] := C a + C b * X + C c * X^2

/-- Determinant of the actual alternative primal image of a rank-one chart. -/
def alternativePolynomial (L : M3) : ℝ[X] :=
  coordinateQuadratic (L 0 0) (L 2 0) (L 1 0) *
    coordinateQuadratic (L 0 1) (L 2 1) (L 1 1) -
    coordinateQuadratic (L 0 2) (L 2 2) (L 1 2)^2

/-- First determinant variation of the actual coordinate action. -/
def directionPolynomial (T : M3) : ℝ[X] :=
  C (T 0 1) + C (T 2 1 - 2*T 0 2) * X +
    C (T 0 0 + T 1 1 - 2*T 2 2) * X^2 +
    C (T 2 0 - 2*T 1 2) * X^3 + C (T 1 0) * X^4

theorem alternativePolynomial_degree (L : M3) :
    (alternativePolynomial L).natDegree ≤ 4 := by
  unfold alternativePolynomial coordinateQuadratic
  compute_degree!

theorem directionPolynomial_degree (T : M3) :
    (directionPolynomial T).natDegree ≤ 4 := by
  unfold directionPolynomial
  compute_degree!

theorem alternativePolynomial_eval (L : M3) (t : ℝ) :
    (alternativePolynomial L).eval t = (primal L (chartOuter t)).det := by
  simp [alternativePolynomial, coordinateQuadratic, primal, decodeLeft, leftVector,
    chartOuter, Matrix.vecMul, dotProduct, Fin.sum_univ_three, Matrix.det_fin_two]
  ring

theorem directionPolynomial_eval (T : M3) (t : ℝ) :
    (directionPolynomial T).eval t =
      determinantDirection (chartOuter t) (primal T (chartOuter t)) := by
  simp [directionPolynomial, determinantDirection, primal, decodeLeft, leftVector,
    chartOuter, Matrix.vecMul, dotProduct, Fin.sum_univ_three]
  ring

theorem directionPolynomial_dual_eval (T : M3) (t : ℝ) :
    -(directionPolynomial T).eval t =
      determinantDirection (chartDual t) (-dual T (chartDual t)) := by
  simp [directionPolynomial, determinantDirection, dual, decodeRight, rightVector,
    chartDual, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- An explicit coordinate action realizing every real quartic. -/
def quarticAction (p : ℝ[X]) : M3 :=
  !![0,p.coeff 0,0; p.coeff 4,0,0; p.coeff 3,p.coeff 1,-p.coeff 2/2]

theorem directionPolynomial_quarticAction (p : ℝ[X]) (hp : p.natDegree ≤ 4) :
    directionPolynomial (quarticAction p) = p := by
  have h := p.as_sum_range_C_mul_X_pow' (by omega : p.natDegree < 5)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, mul_one] at h
  have hc : (0 : ℝ) + 0 - 2 * (-p.coeff 2 / 2) = p.coeff 2 := by ring
  change C (p.coeff 0) + C (p.coeff 1 - 2*0) * X +
    C (0 + 0 - 2*(-p.coeff 2/2)) * X^2 +
    C (p.coeff 3 - 2*0) * X^3 + C (p.coeff 4) * X^4 = p
  rw [hc]
  simpa using h.symm

/-- The two actual coordinate actions are dual for the trace pairing. -/
theorem coordinateActions_trace_cancel (T : M3) (A B : M2)
    (hA : Symmetric A) (hB : Symmetric B) :
    Matrix.trace (primal T A * B) + Matrix.trace (A * (-dual T B)) = 0 := by
  simp [primal, dual, decodeLeft, decodeRight, leftVector, rightVector,
    Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, Matrix.mulVec,
    dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hA 1 0, hB 1 0]
  ring

theorem determinantDirection_smul (a : ℝ) (A E : M2) :
    determinantDirection (a • A) (a • E) = a^2 * determinantDirection A E := by
  simp [determinantDirection, Matrix.smul_apply, smul_eq_mul]
  ring

theorem primal_smul_input (T : M3) (a : ℝ) (A : M2) :
    primal T (a • A) = a • primal T A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [primal, decodeLeft, leftVector, Matrix.vecMul, dotProduct,
      Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] <;> ring

theorem dual_smul_input (T : M3) (a : ℝ) (B : M2) :
    dual T (a • B) = a • dual T B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dual, decodeRight, rightVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul] <;> ring

/-- A symmetric matrix trace-orthogonal to a nonzero PSD matrix cannot have
positive determinant. The symmetric matrix itself need not be PSD. -/
theorem det_nonpos_of_trace_zero_psd (A B : M2) (hA : Symmetric A)
    (hB : PositiveSemidefinite B) (hBne : B ≠ 0)
    (htrace : Matrix.trace (A*B)=0) : A.det ≤ 0 := by
  by_contra! hd
  have htne : A.trace ≠ 0 := by
    intro ht
    have ht' : A 0 0 + A 1 1 = 0 := by simpa [Matrix.trace_fin_two] using ht
    have hd' : 0 < A 0 0 * A 1 1 - A 0 1 ^ 2 := by
      simpa [Matrix.det_fin_two, hA 1 0, pow_two] using hd
    have hc : A 1 1 = -A 0 0 := by linarith
    rw [hc] at hd'
    nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 0 1)]
  rcases lt_or_gt_of_ne htne with ht | ht
  · have hn : Symmetric (-A) := by intro i j; simp [hA i j]
    have hnd : (-A).det = A.det := by simp [Matrix.det_fin_two]
    have hp : PositiveSemidefinite (-A) :=
      psd_two_of_trace_pos_det_nonneg (-A) hn (by simpa using neg_pos.mpr ht)
        (hnd.symm ▸ hd.le)
    have hz : Matrix.trace ((-A)*B)=0 := by simp [htrace]
    have hmul := psd_trace_zero_mul_eq_zero (-A) B hp hB hz
    have hzero := det_zero_of_mul_zero_right_nonzero (-A) B hmul hBne
    rw [hnd] at hzero
    exact (ne_of_gt hd) hzero
  · have hp := psd_two_of_trace_pos_det_nonneg A hA ht hd.le
    have hmul := psd_trace_zero_mul_eq_zero A B hp hB htrace
    exact (ne_of_gt hd) (det_zero_of_mul_zero_right_nonzero A B hmul hBne)

#assert_trust kernel alternativePolynomial_degree
#assert_trust kernel directionPolynomial_degree
#assert_trust kernel alternativePolynomial_eval
#assert_trust kernel directionPolynomial_eval
#assert_trust kernel directionPolynomial_dual_eval
#assert_trust kernel directionPolynomial_quarticAction
#assert_trust kernel coordinateActions_trace_cancel
#assert_trust kernel det_nonpos_of_trace_zero_psd
#print axioms directionPolynomial_quarticAction
#print axioms det_nonpos_of_trace_zero_psd
end
end NLA.Proofs.PF05
