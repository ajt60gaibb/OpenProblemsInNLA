import NLA.Proofs.MF03.PadeDenominatorPolynomial
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! The exact all-order numerator polynomial is the degree-m truncation of
the frozen factorial-series convolution with the original denominator. -/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped BigOperators

namespace NLA.Proofs.MF03

open Polynomial

/-- Literal coefficient truncation of `Q_m f` through degree `m`, with
`f_n=1/(2n)!` as in the frozen normalized Padé statement. -/
noncomputable def cosinePadeNumerator (m : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (m + 1),
    C (∑ i ∈ Finset.range (n + 1),
      (cosinePadeDenominator m).coeff i /
        (((2 * (n - i)).factorial : ℕ) : ℂ)) * X ^ n

theorem cosinePadeNumerator_coeff_le (m n : ℕ) (hn : n ≤ m) :
    (cosinePadeNumerator m).coeff n =
      ∑ i ∈ Finset.range (n + 1),
        (cosinePadeDenominator m).coeff i /
          (((2 * (n - i)).factorial : ℕ) : ℂ) := by
  simp only [cosinePadeNumerator, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single n]
  · simp
  · intro x hx hxn
    have hnex : n ≠ x := Ne.symm hxn
    simp [hnex]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (by omega))).elim

theorem cosinePadeNumerator_coeff_above (m n : ℕ) (hn : m < n) :
    (cosinePadeNumerator m).coeff n = 0 := by
  simp only [cosinePadeNumerator, finsetSum_coeff, coeff_C_mul_X_pow]
  apply Finset.sum_eq_zero
  intro x hx
  have hne : n ≠ x := by
    have hx' := Finset.mem_range.mp hx
    omega
  simp [hne]

theorem cosinePadeNumerator_natDegree_le (m : ℕ) :
    (cosinePadeNumerator m).natDegree ≤ m := by
  apply (natDegree_le_iff_coeff_eq_zero).2
  intro n hn
  exact cosinePadeNumerator_coeff_above m n hn

#assert_trust kernel cosinePadeNumerator_coeff_le
#assert_trust kernel cosinePadeNumerator_coeff_above
#assert_trust kernel cosinePadeNumerator_natDegree_le
#print axioms cosinePadeNumerator_natDegree_le

end NLA.Proofs.MF03
