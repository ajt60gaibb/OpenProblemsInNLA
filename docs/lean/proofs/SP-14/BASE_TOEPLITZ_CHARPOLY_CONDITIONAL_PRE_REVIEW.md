# SP-14 conditional actual Toeplitz charpoly assembly: pre-proof contract

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** frozen for independent review before Lean implementation. This assembles already certified finite algebra with the actual integral-defined Toeplitz parity blocks. The frozen original statement is `lean-statements/NLA/Statements/SP14.lean` (SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00`). The mathematical source is `eigenvalues-and-inverse-problems/SP-14/references/thalhammer-2026-10-09/counterexample.tex` (SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`).

## Exact public Lean theorem

```lean
theorem toeplitz_base_charpoly_of_fourier_pattern (a : Circle → ℂ) (m : ℕ)
    (hpattern : BaseFourierPattern a) :
    (NLA.Statements.SP14.Toeplitz a (2 * m + 1)).charpoly =
      Polynomial.X * (Polynomial.X ^ 2 - 1) ^ m
```

`BaseFourierPattern a` is the explicit even/odd condition in `BaseParityBlocks.lean` (SHA-256 `06ef7ef23d4ea068188c011c680c2c4a43ee8ef6d8a0a8c23dfbac943dc4c5f2`) on the **actual frozen Fourier interval integral**. The theorem is for arbitrary `a` satisfying that condition, and for every `m:ℕ` including `0`. It has no implicit assumption of normality, diagonalizability, or annular extension.

## Proof composition and endpoint

1. `toeplitz_base_parity_blocks a m hpattern` reindexes the actual `Toeplitz a (2*m+1)` by `baseParityEquiv m` into `[[0,baseB m],[baseC m,0]]`. `Matrix.charpoly_reindex` identifies their characteristic polynomials.
2. The generic reviewed `charpoly_offdiagonal_succ m (baseB m) (baseC m)` (frozen source SHA-256 `c503becdb5f9c1cae1da8724c744ebbdf3937316e5536702eaac865de3b88e33`) yields `X · (charpoly(baseC m * baseB m)).comp (X²)` as a polynomial identity, including `X=0`.
3. `baseC_mul_baseB m` and `baseBlock_charpoly m` rewrite the inner polynomial to `(X−1)^m`; polynomial composition then gives `(X²−1)^m`.

For `m=0`, the parity split is `Fin 1 ⊕ Fin 0`; the Toeplitz section is the one-by-one zero matrix because the even Fourier coefficient at zero vanishes, and the formula is `X`. For `m=1`, it is `X³−X`. These are checks of the exact theorem and not substitute proofs.

## Scope boundary

This remains conditional on `BaseFourierPattern a`. It does **not** prove that the actual exterior square-root base symbol has the pattern; constructing that symbol with the correct exterior branch and justifying termwise integration of its infinite boundary series remain analytic obligations. The base symbol has an outer annular extension and therefore cannot itself witness the frozen `SP14.Target`. The final positive/negative-packet counterexample, nonextension, canonical average, selected-root multiplicity, and subsequence gap are separate obligations.
