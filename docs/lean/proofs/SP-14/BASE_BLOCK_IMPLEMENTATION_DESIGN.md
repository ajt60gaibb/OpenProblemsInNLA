# SP-14 base odd-order block proof: Lean implementation design

**Author:** `/root/sp14_base_proof`, 9 October 2026. This records the next exact proof steps after the kernel-checked coefficient convolution in `BaseCoefficient.lean`. It is a design, not a completed Lean theorem.

1. Define the **actual** base circle symbol by the absolutely convergent series `BaseSymbol z = (z:ℂ) * Σ' k, baseCoeff k * (z:ℂ)^(-2k)`. Prove absolute summability and continuity on `Circle`; use the normalized binomial power series on `|s|>1` to identify the exterior analytic branch of `sqrt(1+s⁻¹)`. Its value at the two circle points with `z²=−1` must be the continuous boundary value zero.
2. Prove the frozen integral coefficient identity for every `ℓ:ℤ`: `FourierCoefficient BaseSymbol ℓ = baseCoeff k` when `ℓ=1−2k` for some `k:ℕ`, and zero otherwise. This requires termwise interval integration justified by uniform absolute convergence and exact `Circle.exp` orthogonality. Do not replace the integral-defined `Toeplitz` in the final theorem.
3. For each `m`, define `B : Matrix (Fin (m+1)) (Fin m) ℂ` and `C : Matrix (Fin m) (Fin (m+1)) ℂ` with entries `Bᵢⱼ=c_(j+1−i)` and `Cᵢⱼ=c_(j−i)` using an explicit zero branch for negative subscripts. Prove a parity-reindexing equivalence from `Fin (2m+1)` to `Fin (m+1) ⊕ Fin m` sends the **actual** Toeplitz matrix to `Matrix.fromBlocks 0 B C 0`.
4. Use `baseCoeff_convolution` to prove `(C*B)ᵢⱼ = (if i=j then 1 else 0) + (if i=j+1 then 1 else 0)`. The finite matrix product is the complete convolution because nonzero terms satisfy `i≤k≤j+1`, all within `0,…,m`. Thus `C*B` is unit lower triangular. Its characteristic polynomial is `(X−1)^m` by the pinned Mathlib triangular charpoly theorem after transpose, or directly by triangular determinant.
5. Prove a generic rectangular off-diagonal block lemma over `ℂ`:

   ```text
   charpoly(fromBlocks 0 B C 0)
       = X^(card even − card odd) * det(X² I_odd − C B).
   ```

   Here the card difference is exactly one. A Schur-complement computation over the rational-function field followed by polynomial extensionality is a valid route; the equality must include `X=0`, not rely on pointwise division at nonzero values alone. The pinned Mathlib has `Matrix.det_fromBlocks₁₁/₂₂` in `SchurComplement.lean` and `Matrix.charpoly_mul_comm'` for rectangular products, but no directly named off-diagonal charpoly theorem was found in the inspected source.
6. Combine the five lemmas to conclude, for **every** `m:ℕ`, `(Toeplitz BaseSymbol (2*m+1)).charpoly = X*(X²−1)^m`. Check the `m=0` empty odd block explicitly. No final `Target` theorem follows from this base identity; the base symbol has an outer annular extension.

The power-series equation `(binomialSeries ℂ (1/2))²=1+X` and its coefficient convolution are implemented in `BaseCoefficient.lean`. The lower-bidiagonal characteristic polynomial is implemented in `BaseBlockCharpoly.lean`. The conditional block-selection step is implemented in `BaseProductBlock.lean`, and the unconditional coefficient-defined `G²=I+U` and `C*B=baseBlock` identities are implemented in `BaseCB.lean`. Each compiled under pinned Lean 4.33.1 with LeanCert kernel assertions and only `propext`, `Classical.choice`, and `Quot.sound` reported. The actual circle/Fourier identification, Toeplitz parity reindexing, generic off-diagonal block determinant, and final base-symbol identity remain open.
