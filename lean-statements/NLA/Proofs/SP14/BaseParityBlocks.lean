import NLA.Proofs.SP14.BaseCB
import NLA.Proofs.SP14.BaseParityIndex

/-!
The exact parity blocks of the *actual integral-defined* SP-14 Toeplitz
matrix, conditional on the full base-symbol Fourier coefficient pattern.
The infinite-series analytic proof of that pattern remains separate.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.Proofs.SP14

open NLA.Statements.SP14

/-- Exact integer-frequency pattern of the exterior square-root base
symbol, stated as one even and one odd family. Proving this for the
actual infinite-series symbol remains an analytic obligation. -/
def BaseFourierPattern (a : Circle → ℂ) : Prop :=
  (∀ p : ℤ, FourierCoefficient a (2 * p) = 0) ∧
  (∀ p : ℤ, FourierCoefficient a (1 - 2 * p) =
    if 0 ≤ p then baseCoeff p.toNat else 0)

/-- Under its exact Fourier pattern, the *frozen* Toeplitz section has
the reviewed even/odd blocks with no circulant or normality assumption. -/
theorem toeplitz_base_parity_blocks (a : Circle → ℂ) (m : ℕ)
    (hpattern : BaseFourierPattern a) :
    Matrix.reindex (baseParityEquiv m).symm (baseParityEquiv m).symm
      (Toeplitz a (2 * m + 1)) =
      Matrix.fromBlocks 0 (baseB m) (baseC m) 0 := by
  rcases hpattern with ⟨hEven, hOdd⟩
  ext x y
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₁₁, Matrix.zero_apply, Toeplitz]
      have hfreq :
          ((baseParityEquiv m (Sum.inl i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inl j)).val : ℤ) =
          2 * ((i.val : ℤ) - (j.val : ℤ)) := by simp; ring
      rw [hfreq, hEven]
    | inr j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₁₂, Toeplitz]
      let p : ℤ := (j.val : ℤ) + 1 - (i.val : ℤ)
      have hfreq :
          ((baseParityEquiv m (Sum.inl i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inr j)).val : ℤ) = 1 - 2 * p := by
        simp [p]
        ring
      rw [hfreq, hOdd p]
      by_cases hp : i.val ≤ j.val + 1
      · have hpz : 0 ≤ p := by dsimp [p]; omega
        have hcast : p.toNat = j.val + 1 - i.val := by dsimp [p]; omega
        simp [baseB, baseG, hp, hpz, hcast]
      · have hpz : ¬ 0 ≤ p := by dsimp [p]; omega
        simp [baseB, baseG, hp, hpz]
  | inr i =>
    cases y with
    | inl j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₂₁, Toeplitz]
      let p : ℤ := (j.val : ℤ) - (i.val : ℤ)
      have hfreq :
          ((baseParityEquiv m (Sum.inr i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inl j)).val : ℤ) = 1 - 2 * p := by
        simp [p]
        ring
      rw [hfreq, hOdd p]
      by_cases hp : i.val ≤ j.val
      · have hpz : 0 ≤ p := by dsimp [p]; omega
        have hcast : p.toNat = j.val - i.val := by dsimp [p]; omega
        simp [baseC, baseG, hp, hpz, hcast]
      · have hpz : ¬ 0 ≤ p := by dsimp [p]; omega
        simp [baseC, baseG, hp, hpz]
    | inr j =>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
        Equiv.symm_symm, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Toeplitz]
      have hfreq :
          ((baseParityEquiv m (Sum.inr i)).val : ℤ) -
            ((baseParityEquiv m (Sum.inr j)).val : ℤ) =
          2 * ((i.val : ℤ) - (j.val : ℤ)) := by simp; ring
      rw [hfreq, hEven]

#assert_trust kernel toeplitz_base_parity_blocks
#print axioms toeplitz_base_parity_blocks

end NLA.Proofs.SP14
