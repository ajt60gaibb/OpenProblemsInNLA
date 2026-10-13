# SP-14 actual base Toeplitz identity: independent pre-proof review

**Reviewer:** `/root`, 9 October 2026. **Verdict:** APPROVE the frozen `BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md` as the exact next mathematical contract for the base symbol's Fourier coefficients, actual odd Toeplitz blocks, and all-order characteristic polynomial. This is not approval of the final counterexample or frozen negative `Target`.

The exterior branch is fixed by the absolutely convergent series `g₀(s)=Σ c_r s^(−r)` with limit one at infinity. On the circle, `BaseSymbol(z)=Σ c_r z^(1−2r)` fixes the Fourier signs and ensures coefficient `a_k=c_r` precisely at `k=1−2r`; in particular `a₁=1`, `a₋₁=1/2`, and `a₋₃=−1/8`. The actual frozen Fourier integral and row-minus-column Toeplitz convention must be proved, including convergence and termwise integration, before using these coefficients.

The parity permutation and rectangular orientations are correct. At even row `2i`, odd column `2j+1`, the difference is `1−2(j+1−i)`, giving `Bᵢⱼ=c_(j+1−i)`; at odd row `2i+1`, even column `2j`, it is `1−2(j−i)`, giving `Cᵢⱼ=c_(j−i)`. Thus the reindexed actual matrix has blocks `[0 B; C 0]`. Direct endpoint checks agree: `m=0` gives `[0]` and characteristic polynomial `X`; `m=1` gives the displayed three-by-three matrix and `X³−X`. The `m=2` coefficient and `C B` cancellation signs agree with the reviewed finite algebra.

The rectangular block determinant formula must be proved as a polynomial identity valid at `X=0`; pointwise division at nonzero `X` is insufficient. The already kernel-checked `baseC_mul_baseB` and `baseBlock_charpoly` then provide the finite algebraic factor. The contract explicitly leaves the final nonextension, packet/correction construction, selected-root multiplicities, continuous test function, zero canonical average, and positive empirical gap unproved. The base symbol itself has an outer extension and cannot instantiate the frozen counterexample premise.

| Reviewed input | SHA-256 |
| --- | --- |
| **`BASE_ACTUAL_TOEPLITZ_PRE_REVIEW.md`** | **`0760870797779a198c7fd16e4b1af8d06a398d9384ede2dc20c058a2881674e9`** |
| Frozen `NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Reviewed finite `NLA/Proofs/SP14/BaseCB.lean` | `4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79` |

Changed contract or source bytes reopen this pre-proof review.
