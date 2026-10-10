# SP-14 rectangular off-diagonal characteristic polynomial: pre-proof contract

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** frozen for independent mathematical and signature review before implementation. This is the determinant step in the independently approved `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` (SHA-256 `0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9`). The immutable original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`).

## Exact theorem

For every `m : ℕ`, including `m=0`, and arbitrary complex rectangular matrices `B : Matrix (Fin (m+1)) (Fin m) ℂ` and `C : Matrix (Fin m) (Fin (m+1)) ℂ`, prove:

```lean
theorem charpoly_offdiagonal_succ (m : ℕ)
    (B : Matrix (Fin (m + 1)) (Fin m) ℂ)
    (C : Matrix (Fin m) (Fin (m + 1)) ℂ) :
    (Matrix.fromBlocks
      (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)
      B C (0 : Matrix (Fin m) (Fin m) ℂ)).charpoly =
      Polynomial.X * ((C * B).charpoly.comp (Polynomial.X ^ 2))
```

The output lies in `ℂ[X]`. This is independent of any Fourier assumption and applies to the actual blocks `baseB m`, `baseC m` once `BaseParityBlocks.lean` is certified. The expression `C * B` is `m×m`, so the formula has degree `1+2m`, exactly the size of the block matrix. It is a polynomial equality including `X=0`, not a restricted nonzero-eigenvalue statement.

## Proposed proof

Write `M = [[0,B],[C,0]]` and fix a nonzero `z : ℂ`. The exact evaluation theorem `Matrix.eval_charpoly` gives `χ_M(z)=det([[z I_(m+1),−B], [−C,z I_m]])`. The upper-left block is invertible because `z≠0`. Apply `Matrix.det_fromBlocks₁₁`, obtaining

```text
χ_M(z) = z^(m+1) det(z I_m − z⁻¹ C B)
       = z^(m+1) z^(−m) det(z² I_m − C B)
       = z det(z² I_m − C B).
```

The middle equality uses scalar-matrix multiplication and `det_smul`, valid also when `m=0`. `Matrix.eval_charpoly` and `Polynomial.eval_comp` identify the last determinant with `z · eval z (χ_(CB).comp (X²))`. Therefore the two displayed polynomials agree on all nonzero complex numbers, an infinite set. Apply `Polynomial.eq_of_infinite_eval_eq` (or the equivalent finite-roots theorem) to conclude equality as polynomials. This step supplies equality at `z=0` without division by `z` there. All local invertibility instances used for the Schur complement are discharged from the explicit `z≠0` hypothesis; no theorem statement retains that hypothesis.

If the Schur-complement API makes the scalar inverse cumbersome, an equivalent polynomial-ring block-determinant argument may replace the proof, provided it retains the exact displayed signature, proves equality at zero, and uses only kernel-checked Mathlib lemmas.

## Endpoint and numerical checks

For `m=0`, `B` and `C` are empty, `M` is the `1×1` zero matrix, `(C*B).charpoly=1`, and both sides equal `X`. For `m=1`, take `B=[b₀,b₁]^T`, `C=[c₀,c₁]`: the block matrix has characteristic polynomial `X³−(c₀b₀+c₁b₁)X`, matching `X·χ_(CB)(X²)`. No diagonalizability, normality, spectral pairing assumption, or condition on `B,C` is needed.

## Scope boundary

This theorem alone does not prove the Fourier coefficient pattern of the exterior square-root base symbol, identify the actual Toeplitz blocks, or establish the final SP-14 counterexample. After composing with the conditional actual Toeplitz parity theorem and `baseC_mul_baseB`, the remaining finite step is substitution of `baseBlock_charpoly`, giving `X(X²−1)^m`; the analytic Fourier-pattern proof remains separate. The base symbol has an outer annular extension and is not a witness to the frozen `SP14.Target`.
