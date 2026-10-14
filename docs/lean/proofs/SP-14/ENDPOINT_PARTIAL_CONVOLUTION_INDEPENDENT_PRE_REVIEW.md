# SP-14 endpoint partial convolution: independent pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract `ENDPOINT_PARTIAL_CONVOLUTION_PRE_REVIEW.md` at SHA-256 `dc2f7836d373d1ea5d50b30beb6dfe36ab29613562cc6b93b970fe0d4b437dd7` for a separate scalar Lean gate. This is mathematical and numerical approval before implementation, not a proof of the SP-14 Target.

The canonical manuscript at SHA-256 `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` displays the same `j≥1` identity at lines 735–745. The frozen Target at SHA-256 `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` remains unchanged. The existing Lean definitions are exactly `a_n=Ring.choose(1/2)n` and `b_n=Ring.choose(-1/2)n`; there is no normalization or conjugation mismatch.

I checked the formal-series derivation independently. For `B_k(z)=Σ_{l≤k}b_lz^l`, the binomial recurrence cancels every coefficient below degree `k` in `B_k/2+(1+z)B'_k`; the degree-`k` coefficient is `(k+1/2)b_k`. Thus differentiating `(1+z)^(1/2)B_k` gives `(k+1/2)b_k z^k(1+z)^(-1/2)`. At degree `k+j−1`, the left coefficient is `(k+j)Σ_{d=0}^k a_{d+j}b_{k-d}` and the right is `(k+1/2)b_kb_{j−1}`. Since `j≥1`, division by `k+j` is valid. This includes `k=0`; `j=0` is rightly excluded.

I independently recomputed the exact rational values for all `1≤j≤4`, `0≤k≤3` using rational binomial products; every entry equals the contract table, including signs and the `j−1` shift. The identity itself needs no analytic convergence. It does not prove the subsequent matrix/operator norm, compatible inverse, or frozen negative Target. A Lean implementation must retain the all-index theorem and receive a separate imported kernel/source audit before aggregate import.
