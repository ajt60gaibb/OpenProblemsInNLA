# SP-14 finite inverse truncation: independent imported review

**Disposition:** approve the exact finite triangular compatibility as a partial gate. The completed `L²` inverse and frozen negative `NLA.Statements.SP14.Target` remain open.

I reviewed `EndpointFiniteInverseTruncation.lean` at SHA-256 `b362fe688ccb49f24bbecb227daccbc90d8eaaae8552b8579732414d515509b6` independently of its author against the source-locked [Parseval/completion contract](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md) and its [independent mathematical and numerical pre-review](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_INDEPENDENT_PRE_REVIEW.md). The frozen statement and literal truncation dependency hashes match their reviewed values (`2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` and `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1`). The finite inverse norm dependency is the independently audited SHA-256 `7b2678fd53cededb71dd8e016b75cc56d2c76fbce1ff387a7ebdedb97ed6ec34`.

The exported theorem exactly matches the approved public signature:

```lean
theorem endpointFiniteInverseLp_truncation (r : ℝ)
    (y : SobolevCoeff r) (M N : ℕ) (hMN : M ≤ N) :
    endpointFiniteInverseLp r (sobolevTruncation r M y) N =
      endpointFiniteInverseLp r y M
```

The private pointwise proof unfolds the **actual** finite inverse, applies the audited `physicalCoeff_truncation`, and filters the range `0≤k<N` to `k<M`. The argument includes `M=0`, `M=N`, and arbitrary real `r`; it does not use a replacement finite map. Extensionality then gives equality of the actual continuous additive-circle functions, hence their probability-Haar `Lp` classes. This is the source inverse compatibility required before a tail bound or completion.

I independently imported the frozen module in `/private/tmp/nla-sp14-truncation-independent-audit.lean`, typechecked an exact-signature example, and ran `#assert_trust kernel` under LeanCert `kernel`. Pinned Lean 4.33.1 exited zero; `#print axioms` reported only `[propext, Classical.choice, Quot.sound]`. The source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. The split aggregate `lake build NLA.Proofs` passed 3,135 jobs after import. Aggregate import is approved as this finite identity only.
