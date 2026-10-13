import NLA.Proofs.MF03.PadeNonconstantCoefficients
import Mathlib.Algebra.Polynomial.BigOperators

/-! The exact all-order complex Padé denominator polynomial, built from the
original determinant/Cramer coefficients. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

open Polynomial

/-- The literal normalized denominator with constant coefficient one and
the original Cramer coefficients in degrees `1,…,m`. -/
noncomputable def cosinePadeDenominator (m : ℕ) : Polynomial ℂ :=
  C 1 + ∑ c : Fin m,
    C (cosinePadeNonconstantCoeff m c : ℂ) * X ^ (c.val + 1)

theorem cosinePadeDenominator_coeff_zero (m : ℕ) :
    (cosinePadeDenominator m).coeff 0 = 1 := by
  simp [cosinePadeDenominator, coeff_one, finsetSum_coeff]

theorem cosinePadeDenominator_coeff_fin (m : ℕ) (c : Fin m) :
    (cosinePadeDenominator m).coeff (c.val + 1) =
      (cosinePadeNonconstantCoeff m c : ℂ) := by
  simp only [cosinePadeDenominator, coeff_add,
    finsetSum_coeff, coeff_C_mul_X_pow]
  have hpos : c.val + 1 ≠ 0 := by omega
  simp only [coeff_C, if_neg hpos, zero_add]
  rw [Finset.sum_eq_single c]
  · simp
  · intro x hx hxc
    have hval : c.val ≠ x.val := by
      intro h
      exact hxc (Fin.ext h.symm)
    simp [hval]
  · simp

theorem cosinePadeDenominator_coeff_above (m j : ℕ) (hj : m < j) :
    (cosinePadeDenominator m).coeff j = 0 := by
  have hzero : j ≠ 0 := by omega
  have hneq : ∀ c : Fin m, j ≠ c.val + 1 := by
    intro c
    omega
  simp [cosinePadeDenominator, coeff_one, finsetSum_coeff,
    hzero, hneq]

theorem cosinePadeDenominator_natDegree_le (m : ℕ) :
    (cosinePadeDenominator m).natDegree ≤ m := by
  apply (natDegree_le_iff_coeff_eq_zero).2
  intro j hj
  exact cosinePadeDenominator_coeff_above m j hj

#assert_trust kernel cosinePadeDenominator_coeff_zero
#assert_trust kernel cosinePadeDenominator_coeff_fin
#assert_trust kernel cosinePadeDenominator_coeff_above
#assert_trust kernel cosinePadeDenominator_natDegree_le
#print axioms cosinePadeDenominator_natDegree_le

end NLA.Proofs.MF03
