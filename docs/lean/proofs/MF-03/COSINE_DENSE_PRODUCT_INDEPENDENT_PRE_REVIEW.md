# MF-03 cosine product on the nonzero-sine set: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen narrow contract for implementation. It gives the factorial-series identity and product convergence under `sin(πw)≠0`, not the all-complex product or frozen Padé Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `COSINE_DENSE_PRODUCT_PRE_REVIEW.md` | `ee39fe82fc64a8c365f15b97c7457cb839cce2f05efae918a25f6704763ba98f` |
| Canonical `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| Frozen `NLA.Statements.MF03` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| Audited `CosineProduct.lean` | `a80cd280636110b108e0a13702a55c57d15b739cfc1e73f73bd76eb330689c8a` |
| Pinned Mathlib `EulerSineProd.lean` | `0988322f130952835b0da8d43d24b44c281af10bf149bb869ac750160ec1d5ac` |

The frozen factorial series has coefficients `1/(2j)!`. At `z=−(πw)^2`, its `j`th term is `(-1)^j(πw)^(2j)/(2j)!`, exactly the pinned complex cosine series. This checks the sign and convergence-backed first theorem, with no formal-power-series substitution gap.

For the product, the `k=0` factor is `1−4w²`; in general `cosineFactor(k+1)=4/[π²(2k+1)²]`, so its specialization is `1−4w²/(2k+1)²`. Splitting the finite sine product at `2N` into even and odd denominator indices gives **exactly** `S_(2N)(2w)=S_N(w)C_N(w)`, including `N=0`. The pinned `Complex.tendsto_euler_sin_prod` includes its leading `πw`, so `B_N=πwS_N(w)→sin(πw)` and `A_N=π(2w)S_(2N)(2w)→sin(2πw)`. The finite identity is `A_N=2B_NC_N`; there is no missing factor two. Under the stated nonzero-sine premise, `B_N` is eventually nonzero. Division and the exact double-angle identity yield `C_N→cos(πw)`, which the first theorem identifies with the frozen `waveSeries` value.

At `w=1/2`, the first odd factor is zero and `sin(πw)≠0`, so the result includes a product zero without requiring every finite denominator to be nonzero. At integer `w`, the ratio has a zero limit denominator and this proof does not apply; the contract correctly leaves those points and all-complex coefficient transfer open. No dense-set pointwise result may be promoted to a uniform or coefficient theorem without an additional proof. Schur/tableau denominator bounds, all-order normalized pair existence, and the MF-03 Target remain open.
