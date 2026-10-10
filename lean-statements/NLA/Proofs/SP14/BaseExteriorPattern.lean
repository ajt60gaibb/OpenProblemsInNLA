import NLA.Proofs.SP14.BaseExteriorFourier
import NLA.Proofs.SP14.BaseToeplitzCharpolyConditional

/-!
The exact all-integer Fourier pattern of the normalized exterior base symbol
and its consequent odd-order characteristic polynomial for the actual frozen
Toeplitz sections. The symbol has an outer extension and is not the final
SP-14 counterexample.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- The reviewed exterior series has exactly the even-zero/odd-binomial
Fourier pattern under the frozen integral convention. -/
theorem baseExteriorSymbol_fourier_pattern :
    BaseFourierPattern baseExteriorSymbol := by
  constructor
  · intro p
    rw [baseExteriorSymbol_fourier_tsum]
    have hzero (n : ℕ) :
        baseCoeff n * (if 1 - 2 * (n : ℤ) = 2 * p then 1 else 0) = 0 := by
      have hne : 1 - 2 * (n : ℤ) ≠ 2 * p := by omega
      simp [hne]
    simp_rw [hzero]
    simp
  · intro p
    rw [baseExteriorSymbol_fourier_tsum]
    by_cases hp : 0 ≤ p
    · let r : ℕ := p.toNat
      have hpr : (r : ℤ) = p := Int.toNat_of_nonneg hp
      rw [tsum_eq_single r]
      · simp [hpr, hp, r]
      · intro n hn
        have hne : 1 - 2 * (n : ℤ) ≠ 1 - 2 * p := by
          intro heq
          have hnp : (n : ℤ) = p := by omega
          exact hn (by exact_mod_cast hnp.trans hpr.symm)
        simp [hne]
    · have hzero (n : ℕ) :
          baseCoeff n * (if 1 - 2 * (n : ℤ) = 1 - 2 * p then 1 else 0) = 0 := by
        have hne : 1 - 2 * (n : ℤ) ≠ 1 - 2 * p := by
          intro heq
          have : (n : ℤ) = p := by omega
          omega
        simp [hne]
      simp_rw [hzero]
      simp [hp]

/-- The actual frozen Toeplitz sections of the exterior base symbol have
odd-order characteristic polynomial `X (X²-1)^m`, including `m=0`. -/
theorem baseExteriorSymbol_toeplitz_charpoly (m : ℕ) :
    (Toeplitz baseExteriorSymbol (2 * m + 1)).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m := by
  exact toeplitz_base_charpoly_of_fourier_pattern baseExteriorSymbol m
    baseExteriorSymbol_fourier_pattern

#assert_trust kernel baseExteriorSymbol_fourier_pattern
#assert_trust kernel baseExteriorSymbol_toeplitz_charpoly
#print axioms baseExteriorSymbol_toeplitz_charpoly

end NLA.Proofs.SP14
