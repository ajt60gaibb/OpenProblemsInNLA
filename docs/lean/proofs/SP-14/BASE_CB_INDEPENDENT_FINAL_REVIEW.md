# SP-14 coefficient-defined rectangular blocks: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseCB.lean` as a kernel-checked proof of the approved **unconditional finite coefficient-matrix** identity for every natural `m`. It does not identify those matrices with Fourier-defined blocks of the actual Toeplitz section, prove the base-symbol characteristic polynomial, or prove the final SP-14 counterexample.

The module defines `baseG m` of size `(m+1)×(m+1)` with entry `c_(j−i)` when `i≤j` and zero below the diagonal, where `c_k=Ring.choose(1/2,k)` is the reviewed coefficient. `baseB` selects columns `1,…,m` and all rows, giving size `(m+1)×m` and entry `c_(j+1−i)` with negative indices effectively zero. `baseC` selects rows `0,…,m−1` and all columns, giving size `m×(m+1)` and entry `c_(j−i)`. These orientations match the approved row-minus-column block formulas, but their equality to **actual** Toeplitz blocks still awaits the Fourier bridge.

The private range-convolution lemma converts the already kernel-checked antidiagonal convolution into `Σ_{r=0}^n c_r c_(n−r)`, equal to one at `n=0,1` and zero above. For `i≤j`, the product `(baseG²)ᵢⱼ` is restricted exactly to `i≤k≤j` and reindexed to that complete convolution at `n=j−i`; all selected `k` lie in `0,…,m`. For `i>j`, every product summand is zero. Thus `baseG_square` proves `baseG m * baseG m = I + baseUpperShift m` with no hypothesis, for all `m` including zero. Applying the separately reviewed selection lemma gives `baseC_mul_baseB : baseC m * baseB m = baseBlock m`, also without an input square-identity premise. At `m=2`, the coefficient `c₂=−1/8` appears twice in the upper-right product entry and cancels against `c₁²=1/4`, yielding the required lower, rather than upper, bidiagonal result.

The source uses only finite matrix products and the formal coefficient convolution. It makes no claim that the exterior binomial series converges on the circle, computes the frozen Fourier integral, or identifies `baseB/baseC` with the reordered blocks of `SP14.Toeplitz BaseSymbol`. The odd-block determinant and final actual Toeplitz theorem therefore remain separate obligations.

Pinned `lake build NLA.Proofs.SP14.BaseCB` and a separate imported audit of the five elaborated declarations, `#assert_trust kernel` on both public theorems, and their transitive axioms passed under Lean 4.33.1. Each theorem has exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseCB.lean`** | **`4d08f355b18258aaee4a2a2a7c7546ffee8b13c81d746a8582aea105c7509e79`** |
| `lean-statements/NLA/Proofs/SP14/BaseCoefficient.lean` | `63dcd98bb3a45e77b2b0fd2644d444f9cfe866fb9dae5535d1b7cd1f73081bf4` |
| `lean-statements/NLA/Proofs/SP14/BaseProductBlock.lean` | `dcf88c97cc5fc28466a12220c8849352d4f996ace066a7b98afc1aa502a361b8` |
| `lean-statements/NLA/Proofs/SP14/BaseBlockCharpoly.lean` | `603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_CB_PRE_REVIEW.md` | `ca364c6520afeb3cbf033c7bc77b09a5bb07a06e3c36d25b37813368711141ba` |
| `BASE_CB_INDEPENDENT_PRE_REVIEW.md` | `7751d9d98515a95d947426222d7b89a6a0dd6ee3775151192ca20e41a8c8da68` |
| Independent `/private/tmp/sp14-basecb-independent-audit.lean` | `1b9d5d8f7dd50f053157f16429b3c9a6bd84bbb75ebc47787e2583efc65c77f2` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed source or approved contract bytes reopen this review.
