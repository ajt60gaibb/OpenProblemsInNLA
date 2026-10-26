import NLA.Proofs.TR26.SeparablePencil

/-! Exact degree of a Wronskian of monic polynomials of distinct positive
degrees. The leading coefficient difference is proved nonzero in ℂ. -/
set_option autoImplicit false
set_option leancert.trust "kernel"
noncomputable section
open Polynomial
namespace NLA.Proofs.TR26

def polynomialWronskian (N D : Polynomial ℂ) : Polynomial ℂ :=
  N.derivative * D - N * D.derivative

theorem monicWronskian_natDegree (N D : Polynomial ℂ) (hN : N.Monic) (hD : D.Monic)
    (hNpos : 0 < N.natDegree) (hlt : N.natDegree < D.natDegree) :
    (polynomialWronskian N D).natDegree = N.natDegree + D.natDegree - 1 := by
  have hDpos : 0 < D.natDegree := by omega
  have hNder : N.derivative.natDegree = N.natDegree - 1 := Polynomial.natDegree_derivative N
  have hDder : D.derivative.natDegree = D.natDegree - 1 := Polynomial.natDegree_derivative D
  have hsN : N.natDegree - 1 + D.natDegree = N.natDegree + D.natDegree - 1 := by omega
  have hsD : N.natDegree + (D.natDegree - 1) = N.natDegree + D.natDegree - 1 := by omega
  have hcoefN : N.derivative.coeff (N.natDegree - 1) = (N.natDegree : ℂ) := by
    rw [← hNder, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_derivative, hN, one_mul]
  have hcoefD : D.derivative.coeff (D.natDegree - 1) = (D.natDegree : ℂ) := by
    rw [← hDder, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_derivative, hD, one_mul]
  have hcoef1 : (N.derivative * D).coeff (N.natDegree + D.natDegree - 1) = (N.natDegree : ℂ) := by
    rw [← hsN, Polynomial.coeff_mul_add_eq_of_natDegree_le hNder.le le_rfl,
      hcoefN, Polynomial.coeff_natDegree, hD, mul_one]
  have hcoef2 : (N * D.derivative).coeff (N.natDegree + D.natDegree - 1) = (D.natDegree : ℂ) := by
    rw [← hsD, Polynomial.coeff_mul_add_eq_of_natDegree_le le_rfl hDder.le,
      Polynomial.coeff_natDegree, hN, hcoefD, one_mul]
  have hc : (polynomialWronskian N D).coeff (N.natDegree + D.natDegree - 1) ≠ 0 := by
    rw [polynomialWronskian, Polynomial.coeff_sub, hcoef1, hcoef2]
    apply sub_ne_zero.mpr
    exact_mod_cast Nat.ne_of_lt hlt
  apply le_antisymm
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply Polynomial.natDegree_mul_le.trans
      omega
    · apply Polynomial.natDegree_mul_le.trans
      omega
  · exact Polynomial.le_natDegree_of_ne_zero hc

#assert_trust kernel monicWronskian_natDegree
#print axioms monicWronskian_natDegree
end NLA.Proofs.TR26
