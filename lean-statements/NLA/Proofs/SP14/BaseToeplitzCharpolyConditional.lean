import NLA.Proofs.SP14.BaseOffdiagonalCharpoly
import NLA.Proofs.SP14.BaseBlockCharpoly

/-!
The all-odd-order characteristic polynomial of the actual integral-defined
SP-14 Toeplitz sections, conditional on the exterior base Fourier pattern.
The analytic proof of that pattern for the base symbol remains separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Polynomial

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- Exact odd Toeplitz characteristic polynomial, with its analytic Fourier
coefficient identification stated explicitly as a hypothesis. -/
theorem toeplitz_base_charpoly_of_fourier_pattern (a : Circle → ℂ) (m : ℕ)
    (hpattern : BaseFourierPattern a) :
    (Toeplitz a (2 * m + 1)).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m := by
  have hblocks := toeplitz_base_parity_blocks a m hpattern
  calc
    (Toeplitz a (2 * m + 1)).charpoly =
        (Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
          (Toeplitz a (2 * m + 1))).charpoly :=
      (Matrix.charpoly_reindex (baseParityEquiv m).symm
        (Toeplitz a (2 * m + 1))).symm
    _ = (Matrix.fromBlocks
          (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
          (baseB m) (baseC m) (0 : Matrix (Fin m) (Fin m) ℂ)).charpoly := by
      rw [hblocks]
    _ = Polynomial.X *
          ((baseC m * baseB m).charpoly.comp (Polynomial.X ^ 2)) :=
      charpoly_offdiagonal_succ m (baseB m) (baseC m)
    _ = Polynomial.X * ((((Polynomial.X : Polynomial ℂ) - 1) ^ m).comp
          (Polynomial.X ^ 2)) := by
      rw [baseC_mul_baseB, baseBlock_charpoly]
    _ = Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m := by
      simp

#assert_trust kernel toeplitz_base_charpoly_of_fourier_pattern
#print axioms toeplitz_base_charpoly_of_fourier_pattern

end NLA.Proofs.SP14
