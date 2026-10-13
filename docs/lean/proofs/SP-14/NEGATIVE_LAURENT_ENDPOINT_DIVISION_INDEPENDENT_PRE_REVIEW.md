# SP-14 finite negative Laurent endpoint division: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen exact contract for implementation. It proves finite algebraic divisibility of the actual negative Laurent correction at the contact point; it does not prove a Wiener estimate or the SP-14 Target.

| Reviewed input | SHA-256 |
| --- | --- |
| `NEGATIVE_LAURENT_ENDPOINT_DIVISION_PRE_REVIEW.md` | `1d8f584838935b6ebc314bb5a12a3e5b981001ad1a045e1ea8dd7317c03ccbaa` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Audited finite Laurent source | `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b` |

The audited `negativeLaurent u p` is `Σ_{j=1}^u p_j s^{-j}` with real coefficients. A factor `(1+s)` times a same-index negative Laurent `Q` has constant coefficient `q₁`, so requiring `q₁=0` is necessary. Its remaining coefficients are `q_j+q_{j+1}` with `q_{u+1}=0`. Recursively set `q_{j+1}=p_j−q_j`. Then the final equation `p_u=q_u` is equivalent, with the exact alternating signs, to the actual hypothesis `P(-1)=Σ_{j=1}^u(-1)^j p_j=0`. This proves equality for every circle point, using nonzero circle coordinates for the exponent shift. No formal division at `s=-1` is used.

For `u=0`, the unique empty vector gives `0=(1+s)0`. For `u=1`, contact forces `p₁=0` and the only `q` is zero. For `u=2`, `p=(t,t)` gives `q=(0,t)` and `t(s^{-1}+s^{-2})=(1+s)t s^{-2}`; this checks the shift and signs. The proposed theorem retains the same `Fin u` size, real coefficients, actual contact hypothesis, and all-circle conclusion. It does not assume the factorization as an input.

Implementation must preserve these endpoints and the exact one-based indexing. Keep the new source unimported until a separate source/signature/LeanCert kernel audit. The weighted convolution, five source smallness bounds and final counterexample remain open.
