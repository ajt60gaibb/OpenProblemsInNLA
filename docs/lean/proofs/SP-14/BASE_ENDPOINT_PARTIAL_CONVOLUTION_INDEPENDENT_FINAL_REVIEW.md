# SP-14 base endpoint partial convolution: independent final review

**Independent mathematical/source/kernel reviewer:** `/root`, 10 October 2026. **Proof author:** `/root/sp14_base_proof`. **Verdict:** APPROVE the frozen scalar endpoint convolution theorem for aggregate import. The full analytic projection and frozen SP-14 counterexample remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/BaseEndpointPartialConvolution.lean` | `6e3ead11ba99fe781d8df49eaa4cdf7f920170488f72ebfece1f97b41c68f324` |
| Exact source and numeric precontract `ENDPOINT_PARTIAL_CONVOLUTION_PRE_REVIEW.md` | `dc2f7836d373d1ea5d50b30beb6dfe36ab29613562cc6b93b970fe0d4b437dd7` |
| Separate imported audit `/private/tmp/sp14-base-endpoint-partial-convolution-independent-audit.lean` | `177ac621152daeb67844afa008bcf17d2f12698cf9e2f6eabe75d5d91db77737` |

The public theorem has exactly the independently pre-reviewed identity for **every** `k:ℕ`, `j≥1`:

```text
Σ_{d=0}^k baseCoeffReal(d+j) baseInverseCoeff(k−d)
  = ((k+1/2)/(k+j)) baseInverseCoeff(k) baseInverseCoeff(j−1).
```

The source defines the finite polynomial `B_k=Σ_{l≤k} b_l X^l`, proves the exact binomial recurrence and `(1+X) B'_k + B_k/2=(k+1/2)b_k X^k`, and transports this identity into formal power series. Its formal derivative of `(1+X)^(1/2) B_k` is `(k+1/2)b_k X^k(1+X)^(-1/2)`. Extracting coefficient `k+j−1` gives the displayed sum and right side, then divides by the positive cast of `k+j`. The coefficient reversal in the finite sum is checked with `Finset.sum_range_reflect`; its natural subtraction is used only where `d≤k`. No analytic convergence or branch identity is assumed. The source matches the canonical manuscript and the independently checked 16 rational table entries in the precontract, including `k=0` and `j=1`.

The agent's direct pinned Lean 4.33.1 build passed with two linter warnings. My separate imported audit reconstructed the complete public signature from the precontract, ran LeanCert `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. This lemma alone does not identify the actual endpoint matrix, establish a Sobolev operator bound, or prove the frozen negative Target. Changed source bytes require a new review.
