import NLA.Proofs.SP14.BaseParityBlocks

/-!
The all-size characteristic polynomial of a rectangular off-diagonal block
matrix. This is finite algebra independent of the base symbol's Fourier series.
-/
set_option autoImplicit false
set_option leancert.trust "kernel"

open scoped Matrix Polynomial

namespace NLA.Proofs.SP14

private theorem charpoly_comp_sq {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℂ) :
    D.charpoly.comp (Polynomial.X ^ 2) =
      (Matrix.scalar n (Polynomial.X ^ 2) - D.map Polynomial.C).det := by
  rw [Matrix.charpoly, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
  congr 1
  ext i j
  by_cases hij : i = j <;>
    simp [Matrix.charmatrix, Matrix.scalar_apply, hij]

private theorem det_scalar_X (n : ℕ) :
    (Matrix.scalar (Fin n) (Polynomial.X : ℂ[X])).det = Polynomial.X ^ n := by
  simp [Matrix.scalar, Matrix.det_diagonal]

/-- Rectangular off-diagonal block characteristic polynomial, including
the empty lower block at `m=0` and the value `X=0`. -/
theorem charpoly_offdiagonal_succ (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin m) ℂ)
    (C : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    (Matrix.fromBlocks
      (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      B C (0 : Matrix (Fin m) (Fin m) ℂ)).charpoly =
      Polynomial.X * ((C * B).charpoly.comp (Polynomial.X ^ 2)) := by
  classical
  let BP : Matrix (Fin (m + 1)) (Fin m) ℂ[X] := B.map Polynomial.C
  let CP : Matrix (Fin m) (Fin (m + 1)) ℂ[X] := C.map Polynomial.C
  let T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ[X] := Matrix.scalar _ Polynomial.X
  let S : Matrix (Fin m) (Fin m) ℂ[X] := Matrix.scalar _ Polynomial.X
  let A : Matrix (Fin (m + 1) ⊕ Fin m) (Fin (m + 1) ⊕ Fin m) ℂ[X] :=
    Matrix.fromBlocks T (-BP) (-CP) S
  let N : Matrix (Fin (m + 1) ⊕ Fin m) (Fin (m + 1) ⊕ Fin m) ℂ[X] :=
    Matrix.fromBlocks 1 BP 0 S
  have hA : A.det = (Matrix.fromBlocks
      (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      B C (0 : Matrix (Fin m) (Fin m) ℂ)).charpoly := by
    simp [A, Matrix.charpoly, Matrix.charmatrix_fromBlocks,
      Matrix.charmatrix_zero, BP, CP, T, S]
  have hN : N.det = Polynomial.X ^ m := by
    simp [N, S]
  have hprod : A * N = Matrix.fromBlocks T 0 (-CP) (S * S - CP * BP) := by
    have hcomm : T * BP = BP * S :=
      Matrix.scalar_comm Polynomial.X (fun _ => Commute.all _ _) BP
    simp only [A, N, Matrix.fromBlocks_multiply]
    simp
    constructor
    · rw [hcomm]
      simp
    · abel
  have hSS : S * S - CP * BP =
      Matrix.scalar (Fin m) (Polynomial.X ^ 2) - (C * B).map Polynomial.C := by
    simp [S, CP, BP, Matrix.map_mul, pow_two]
  have hdet : (A * N).det = Polynomial.X ^ (m + 1) *
      ((C * B).charpoly.comp (Polynomial.X ^ 2)) := by
    rw [hprod, Matrix.det_fromBlocks_zero₁₂, hSS, ← charpoly_comp_sq,
      show T.det = Polynomial.X ^ (m + 1) from det_scalar_X (m + 1)]
  rw [Matrix.det_mul, hA, hN] at hdet
  apply (Polynomial.isRegular_X_pow m).right.eq_iff.mp
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdet

#assert_trust kernel charpoly_offdiagonal_succ
#print axioms charpoly_offdiagonal_succ

end NLA.Proofs.SP14
