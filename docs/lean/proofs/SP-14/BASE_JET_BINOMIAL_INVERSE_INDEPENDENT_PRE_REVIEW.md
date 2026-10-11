# SP-14 explicit base-Jacobian binomial inverse: independent mathematical and numerical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract for a separate Lean implementation. This is a finite source-preconditioner identity, not the actual-background Sobolev isomorphism or the SP-14 target.

| Reviewed input | SHA-256 |
| --- | --- |
| `BASE_JET_BINOMIAL_INVERSE_PRE_REVIEW.md` | `2e56799ab554b33a04bf8c7ec8c8729095c4e8a21b82d2b0046781f3bc3476` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Audited `BaseJetTriangular.lean` | `a1cff804e204a656bed6f0b45d06d0d0e0f238d385468bcda4384b72cd790ccc` |
| Approved actual-background precontract | `5b52aaf4103ac675f74797cbd17ba63c39fdca5556b5203076c15a5cd889db68` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |

The existing `baseJetMatrix q` has output row `k`, correction column `d`, and entry `−2(k+1) binom(1/2,d−k)` when `k≤d`. The proposed inverse has correction row `d`, output column `k`, and entry `−(1/2) binom(−1/2,k−d)/(k+1)` when `d≤k`. Multiplying in the first order gives `(k+1)/(j+1)` times the coefficient convolution at `j−k`; the prefactor is one whenever the convolution can be nonzero. Multiplying in the other order cancels `(k+1)` within each summand. Both products therefore equal the square identity once `Σ_{r=0}^n binom(1/2,r)binom(−1/2,n−r)=δ_{n0}` is proved. This is the exact coefficient identity of `(1+X)^(1/2)(1+X)^(−1/2)=1`, including `n=0`.

The source's finite preconditioner formula has the same negative sign, `−1/2` binomial exponent, and division by the output index `k+1`. Its sum is over `k≥d`, so the matrix is upper triangular in the specified row/column orientation. The explicit solve conclusion correctly identifies the previously audited unique inverse solve, not merely a new arbitrary right inverse. At `q=0`, the unique empty matrices and vector satisfy both identities.

I independently computed the proposed matrices with exact rational arithmetic for `q=0,1,2,3` and checked both products. For `q=2`, `M=[[-2,-1],[0,-4]]` and `N=[[-1/2,1/8],[0,-1/4]]`. For `q=3`, the inverse rows give `v₀=−x₀/2+x₁/8−x₂/16`, `v₁=−x₁/4+x₂/12`, `v₂=−x₂/6`; both products are identity. These finite checks validate indexing and signs; the Lean theorem must prove all natural `q` by coefficient convolution and exact finite algebra.

The module may use the audited nonsingularity of `baseJetMatrix` to derive one product from the other, but both public matrix identities and the explicit `baseJetSolve` equality are required. It must not assume the source inverse as a premise, alter the original target, or claim the limiting Jacobian, conformal map, compatible Sobolev inverses, or counterexample. A frozen Lean source needs an independent signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit before aggregate import. Changed contract bytes reopen this review.
