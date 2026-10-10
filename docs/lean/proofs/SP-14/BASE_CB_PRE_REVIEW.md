# SP-14 finite rectangular block product: pre-proof review

**Author:** `/root/sp14_base_proof`, 9 October 2026. **Status:** proposed for independent mathematical review before implementing the unconditional product identity. This is a finite matrix component of the separately reviewed base odd-characteristic-polynomial target.

Let `c_k = binom(1/2,k) : ℂ` for `k≥0` and define `c_k=0` for negative integer `k`. For each `m:ℕ`, let `G : Matrix (Fin (m+1)) (Fin (m+1)) ℂ` have entries `Gᵢⱼ=c_(j−i)`, let `B : Matrix (Fin (m+1)) (Fin m) ℂ` have entries `Bᵢⱼ=c_(j+1−i)`, and let `C : Matrix (Fin m) (Fin (m+1)) ℂ` have entries `Cᵢⱼ=c_(j−i)`. These are exactly the even-row/odd-column and odd-row/even-column blocks of the **row-minus-column** Toeplitz section of the base symbol after the Fourier coefficient identity is proved. The proposed theorem is unconditional finite algebra:

```text
∀ m:ℕ, C(m) * B(m) = baseBlock(m),
baseBlock(m)ᵢⱼ = 1 if i=j or i=j+1; 0 otherwise.
```

The proof uses the already kernel-checked universal convolution `Σ_{r+s=n} c_r c_s = 1` at `n=0,1` and `0` otherwise. For `i,j<m`, the summand in `(CB)ᵢⱼ` is nonzero only if `i≤k≤j+1`; if this interval is empty, the entry is zero. Otherwise `r=k−i` runs through `0,…,j+1−i`, so the full finite sum is the convolution coefficient at `n=j+1−i`. It equals one when `n=0` (`i=j+1`) or `n=1` (`i=j`) and zero otherwise. Equivalently, the full square `G²` is `I+U` for the upper unit shift `U`, and `C`/`B` select its first `m` rows and last `m` columns. The selection step must use precisely those row/column maps; swapping them reverses the bidiagonal orientation.

At `m=0`, `B` and `C` have empty `Fin 0` dimensions and their product is the empty matrix, equal to `baseBlock 0`. At `m=1`, `C=[1,1/2]`, `B=[1/2,1]ᵀ`, so `CB=[1]`. At `m=2`, `CB=[[1,0],[1,1]]`; in particular the off-diagonal one is **below** the diagonal. The `c₂=−1/8` terms cancel in the upper-right entry.

This theorem neither defines the actual circle symbol nor proves its Fourier integrals. The final base identity still requires the Fourier bridge, parity reindexing, off-diagonal block determinant, and assembly into `Toeplitz BaseSymbol`; the base symbol has an outer annular extension and is not the final counterexample.
