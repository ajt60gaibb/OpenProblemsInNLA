# SP-14 actual base symbol to odd Toeplitz characteristic polynomial: pre-proof contract

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** proposed for independent mathematical/numerical review before Lean implementation. This contract connects the previously reviewed finite binomial/block algebra to the **actual integral-defined** `NLA.Statements.SP14.Toeplitz`. It is a base-symbol identity, not a proof of the final counterexample or `Target`.

## Frozen source and proposed Lean declarations

The immutable statement boundary is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`). The mathematical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`), particularly its normalized exterior `g₀` and exact finite algebra around Proposition 2.1. The canonical README's retained base identity is the same.

Let `cₖ = NLA.Proofs.SP14.baseCoeff k = Ring.choose (1/2:ℂ) k`. Construct `BaseSymbol : Circle → ℂ` as the uniformly and absolutely convergent boundary series

```text
BaseSymbol(z) = Σ_{r≥0} c_r z^(1−2r)
              = z Σ_{r≥0} c_r (z²)^(-r).
```

On `|s|>1`, `g₀(s)=Σ c_r s^(-r)` is holomorphic, tends to `1` at infinity, and satisfies `g₀(s)²=1+s⁻¹`. Its continuous values on `|s|=1`, including `g₀(−1)=0`, define the boundary function in `BaseSymbol`. This fixes the exterior square-root branch. The relation `BaseSymbol(z)²=z²+1` alone would permit the wrong sign and is not an adequate definition. The base symbol has an outer one-sided annular extension, obtained from `z ↦ z g₀(z²)` on `|z|>1` and continuous to `|z|=1`.

The proposed final declaration, for **every** `m:ℕ` including `0`, is exactly

```lean
(NLA.Statements.SP14.Toeplitz BaseSymbol (2*m+1)).charpoly
  = Polynomial.X * (Polynomial.X^2 - 1)^m
```

Its `Toeplitz` must be the frozen Fourier-integral definition, not an auxiliary matrix. No assumption about normality, diagonalizability, test function, or annular nonextension enters this theorem.

## Required intermediate theorems and proof route

1. **Series and Fourier boundary.** Prove `∑ ‖c_r‖ < ∞` (the half-binomial coefficients have `O(r^(-3/2))` decay) and uniform absolute convergence of the circle series. For every **integer** frequency `k`, prove the exact frozen real-interval coefficient

   ```text
   FourierCoefficient BaseSymbol k = c_r  if k=1−2r for some r:ℕ,
                                 = 0    otherwise.
   ```

   The frequencies `1−2r` are pairwise distinct. Termwise integration requires a proved uniform or dominated convergence step, plus the exact orthogonality of `e^{i(1−2r−k)t}` on `[0,2π]` under the factor `1/(2π)`. The sign `e^(−ikt)` and genuine `Circle.exp t=e^{it}` are binding. In particular `a₁=1`, `a₋₁=1/2`, `a₋₃=−1/8`, and every even frequency and every frequency above `1` vanishes.

2. **Actual parity blocks.** For `n=2m+1`, reindex `Fin n` by the equivalence sending the first `m+1` coordinates to `0,2,…,2m` and the last `m` coordinates to `1,3,…,2m−1`. Using the Fourier theorem and frozen row-minus-column convention, prove the reindexed *actual* matrix is

   ```text
   Matrix.fromBlocks 0 (baseB m) (baseC m) 0.
   ```

   Here `baseB` has shape `(m+1)×m` and entries `c_(j+1−i)` with negative subscripts zero; `baseC` has shape `m×(m+1)` and entries `c_(j−i)` with negative subscripts zero. This orientation puts `a₁=1` below the main diagonal and `a₋₁=1/2` above it. The `m=0` case is a one-by-one zero matrix with an empty odd block.

3. **Off-diagonal determinant.** Prove, as a genuine complex-polynomial identity for rectangular `B,C` of these sizes,

   ```text
   charpoly(fromBlocks 0 B C 0)
     = X * det(X² I_(Fin m) − C B).
   ```

   This equality must hold at `X=0` and preserve algebraic multiplicity; a pointwise Schur complement restricted to nonzero spectral parameters must be extended by polynomial identity. The pinned Mathlib's `Matrix.det_fromBlocks₁₁/₂₂`, `Matrix.charpoly_mul_comm'`, and triangular determinant tools may be used, but no off-diagonal formula is assumed as an axiom.

4. **Finish via certified finite algebra.** The kernel-checked `baseC_mul_baseB` gives `baseC m * baseB m = baseBlock m`. The `baseBlock m` is unit lower bidiagonal, so `det(X²I−baseBlock m)=(X²−1)^m` by its triangular form. Combine with the parity reindex theorem and characteristic-polynomial invariance under a finite index equivalence. This proves the displayed final equality for all `m` without dividing by `X` or assuming a complete eigenbasis.

The existing finite component proofs have normal Lean foundation axiom lists only: `BaseCoefficient.lean` proves the half-binomial convolution, `BaseCB.lean` proves `G²=I+U` and `C B=baseBlock`, and `BaseBlockCharpoly.lean` proves `charpoly(baseBlock)=(X−1)^m`. These finite theorems do **not** by themselves identify any frozen Fourier integral or the actual Toeplitz characteristic polynomial.

## Numerical and scope checks

At `m=0`, the actual matrix is `[0]` and the formula is `X`. At `m=1`, the actual matrix is `[[0,1/2,0],[1,0,1/2],[0,1,0]]`, giving `X³−X`. At `m=2`, the `−1/8` coefficient appears on the third superdiagonal of the five-by-five matrix, and the formula is `X⁵−2X³+X`; the two `−1/8` contributions cancel the upper-right entry of `C B`. These are sign and endpoint checks, not substitutes for the all-`m` proof.

The base symbol admits an **outer** extension and therefore fails the “neither one-sided extension” premise of `OriginalConjecture`. The final counterexample requires its separate positive/negative packets, corrections, actual failure of both annular extensions, selected-root multiplicities at `±1`, the exact finite lower bound `⌊2^(−10000)m_j⌋/(2m_j+1)`, a continuous compactly supported test separated from the final symbol range, zero canonical average, and an eventual positive gap. Only then can the already proved conditional `target_of_subsequence_gap` establish the frozen negative `SP14.Target`. No base identity here discharges those obligations.
