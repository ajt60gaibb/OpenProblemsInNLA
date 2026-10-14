# SP-14 finite rectangular block product: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BASE_CB_PRE_REVIEW.md` for implementation of the unconditional finite identity `C(m)*B(m)=baseBlock(m)` for every natural `m`. This is a matrix-algebra component, not Fourier identification, an actual Toeplitz characteristic-polynomial theorem, or the final counterexample.

The coefficient convention is exact: `c_k=binom(1/2,k)` for `k≥0`, and zero at negative integer indices. The previously reviewed formal-series theorem gives `Σ_{r+s=n}c_rc_s=1` for `n=0,1` and zero for every `n≥2`; `c₀=1`, `c₁=1/2`, and `c₂=−1/8`. The proposed shapes are consistent: `G` is `(m+1)×(m+1)`, `B` is `(m+1)×m`, `C` is `m×(m+1)`, and `CB` is `m×m`. These are the even-row/odd-column and odd-row/even-column index formulas **conditional on a later Fourier bridge** for the row-minus-column Toeplitz section: `Bᵢⱼ=c_(j+1−i)`, `Cᵢⱼ=c_(j−i)`.

For `i,j<m`, `(CB)ᵢⱼ=Σ_{k=0}^m c_(k−i)c_(j+1−k)`. A nonzero summand requires `i≤k≤j+1`. If `j+1<i`, the sum is zero. Otherwise that full interval lies inside `0≤k≤m`, and with `r=k−i`, `s=j+1−k` it is precisely the complete convolution coefficient at `n=j+1−i`. Hence the result is one when `i=j+1` or `i=j`, and zero otherwise: the first off-diagonal one is **below**, not above, the diagonal. Equivalently, the first `m` rows and columns `1,…,m` of `G²=I+U` give `CB`; those selections have the stated orientation.

The boundary cases check out. At `m=0`, the product and `baseBlock 0` are both empty matrices. At `m=1`, `C=[1,1/2]` and `B=[1/2,1]ᵀ`, giving `[1]`. At `m=2`,

```text
B = [[1/2, -1/8], [1, 1/2], [0, 1]],
C = [[1, 1/2, -1/8], [0, 1, 1/2]],
CB = [[1, 0], [1, 1]].
```

The upper-right entry is `−1/8+1/4−1/8=0`; both appearances of the negative `c₂` are necessary. The general argument uses only finite coefficient sums and has no analytic limit or large-order approximation. It leaves the actual symbol, its Fourier integrals, parity reindexing, odd-block determinant, and final Toeplitz theorem unproved. The base symbol has an outer extension, so even that eventual theorem would not prove `SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`docs/lean/proofs/SP-14/BASE_CB_PRE_REVIEW.md`** | **`ca364c6520afeb3cbf033c7bc77b09a5bb07a06e3c36d25b37813368711141ba`** |
| Frozen `lean-statements/NLA/Proofs/SP14/BaseCoefficient.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| Frozen `lean-statements/NLA/Proofs/SP14/BaseBlockCharpoly.lean` | `603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_ODD_CHARPOLY_INDEPENDENT_PRE_REVIEW.md` | `f7a63e4782b5c29f27fbdac58ffe1ee7e0d517827492a33a1816e37339d375c1` |

Changed source or proposed contract bytes reopen this pre-proof review.
