# SP-14 selected rectangular block: independent Lean source review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `BaseProductBlock.lean` as an exact **conditional** finite matrix-selection lemma. It assumes `G²=I+U`; it does not prove that identity for the binomial coefficient matrix, identify actual `C*B`, establish Fourier coefficients, or prove the Toeplitz characteristic polynomial or final SP-14 `Target`.

`baseUpperShift m` is the `(m+1)×(m+1)` matrix with a one exactly at column `row+1`. For an arbitrary square `G` of that size, `base_selected_product` assumes `G*G=1+baseUpperShift m`. Its left factor `G.submatrix Fin.castSucc id` selects rows `0,…,m−1` and all columns, matching the proposed `C`; its right factor `G.submatrix id Fin.succ` selects all rows and columns `1,…,m`, matching `B`. The product's `(i,j)` entry is the `(i,j+1)` entry of `G²`. On `I+U`, this is one if `i=j+1` from `I`, one if `i=j` from `U`, and zero otherwise. This is precisely the previously reviewed `baseBlock m`, with the off-diagonal one **below** the diagonal. The matrices and theorem type remain valid at `m=0`, where the selected product and block are empty.

The source proof uses only the explicit `hG` equality, matrix entry extensionality, and index arithmetic. Its hypothesis is visible in the elaborated public signature; no unconditional coefficient convolution is smuggled into it. The next module must construct the coefficient matrix `G` and prove its square identity, then connect the selected matrices to the actual Toeplitz blocks after Fourier identification.

Pinned `lake build NLA.Proofs.SP14.BaseProductBlock` and a separate imported audit of `#check`, `#assert_trust kernel`, and `#print axioms` passed under Lean 4.33.1. The theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/BaseProductBlock.lean`** | **`dcf88c97cc5fc28466a12220c8849352d4f996ace066a7b98afc1aa502a361b8`** |
| `lean-statements/NLA/Proofs/SP14/BaseBlockCharpoly.lean` | `603dcc3f95f21c6d3c7646b47f1d280996a81ff95e813d82c31541ef9d10db7f` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `BASE_CB_PRE_REVIEW.md` | `ca364c6520afeb3cbf033c7bc77b09a5bb07a06e3c36d25b37813368711141ba` |
| `BASE_CB_INDEPENDENT_PRE_REVIEW.md` | `7751d9d98515a95d947426222d7b89a6a0dd6ee3775151192ca20e41a8c8da68` |
| Independent `/private/tmp/sp14-baseproductblock-independent-audit.lean` | `3b35146b6811d4927a8cbdf6efa32770f461a82b0ed58abd2fd616c77e46912f` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |

Changed theorem or approved contract bytes reopen review.
