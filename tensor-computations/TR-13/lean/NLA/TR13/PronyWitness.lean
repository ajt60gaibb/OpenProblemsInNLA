import NLA.TR13.PronyPolynomial
import Mathlib.Algebra.Group.Fin.Basic

noncomputable section
open scoped BigOperators
open Polynomial Matrix

namespace NLA.TR13

/-- Periodic moments whose recurrence is `X^r - 1`. -/
def periodicMoment (r i : ℕ) : ℂ := if i % r = 0 then 1 else 0

lemma periodicMoment_add (r i : ℕ) : periodicMoment r (i + r) = periodicMoment r i := by
  simp [periodicMoment]

lemma periodicMoment_matrix_entry (r : ℕ) [NeZero r] (i j : Fin r) :
    momentMatrix r (periodicMoment r) i j = if j = -i then 1 else 0 := by
  have h : (i.val + j.val) % r = 0 ↔ j = -i := by
    change (i + j).val = (0 : Fin r).val ↔ _
    rw [← Fin.ext_iff]
    simpa only [add_comm] using (add_eq_zero_iff_eq_neg : j + i = 0 ↔ j = -i)
  simp [momentMatrix, periodicMoment, h]

lemma periodicMoment_matrix_sq (r : ℕ) [NeZero r] :
    momentMatrix r (periodicMoment r) * momentMatrix r (periodicMoment r) = 1 := by
  classical
  ext i j
  simp only [Matrix.mul_apply, periodicMoment_matrix_entry]
  rw [Finset.sum_eq_single (-i)]
  · simp [Matrix.one_apply, eq_comm]
  · intro b _ hb
    simp [hb]
  · simp

lemma periodicMoment_det_ne_zero (r : ℕ) [NeZero r] :
    (momentMatrix r (periodicMoment r)).det ≠ 0 := by
  have he := congrArg Matrix.det (periodicMoment_matrix_sq r)
  rw [Matrix.det_mul, Matrix.det_one] at he
  intro hz
  simp [hz] at he

lemma periodicMoment_shift (r : ℕ) [NeZero r] :
    shiftedMoments r (periodicMoment r) =
      momentMatrix r (periodicMoment r) *ᵥ Pi.single 0 1 := by
  ext i
  simp [shiftedMoments, periodicMoment_add, momentMatrix,
    Matrix.mulVec, dotProduct, Pi.single_apply]

lemma periodicMoment_coefficients (r : ℕ) [NeZero r] :
    pronyCoefficients r (periodicMoment r) =
      (momentMatrix r (periodicMoment r)).det • Pi.single 0 1 := by
  unfold pronyCoefficients
  rw [periodicMoment_shift, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]

lemma periodicMoment_polynomial (r : ℕ) [NeZero r] :
    pronyPolynomial r (periodicMoment r) =
      C (momentMatrix r (periodicMoment r)).det * (X ^ r - 1) := by
  classical
  unfold pronyPolynomial
  rw [periodicMoment_coefficients]
  have he : Polynomial.ofFn r
      ((momentMatrix r (periodicMoment r)).det • (Pi.single 0 1 : Fin r → ℂ)) =
      C (momentMatrix r (periodicMoment r)).det := by
    rw [Polynomial.ofFn_eq_sum_monomial]
    simp [Pi.smul_apply, Pi.single_apply, apply_ite, Finset.sum_ite_eq']
  rw [he]
  ring

lemma periodicMoment_certificate_ne_zero {r : ℕ} (hr : 0 < r) :
    pronyCertificate r (periodicMoment r) ≠ 0 := by
  let : NeZero r := ⟨by omega⟩
  have hdet := periodicMoment_det_ne_zero r
  have hsep : (pronyPolynomial r (periodicMoment r)).Separable := by
    rw [periodicMoment_polynomial]
    apply Polynomial.Separable.unit_mul
    · exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hdet)
    · exact Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast (ne_of_gt hr))
  have hdeg := pronyPolynomial_natDegree hr (periodicMoment r) hdet
  unfold pronyCertificate
  apply mul_ne_zero hdet
  intro hz
  have hz' : Polynomial.resultant (pronyPolynomial r (periodicMoment r))
      (pronyPolynomial r (periodicMoment r)).derivative = 0 := by
    simpa [hdeg, Polynomial.natDegree_derivative] using hz
  exact (Polynomial.resultant_eq_zero_iff.mp hz').2 hsep

end NLA.TR13
