# SP-14 finite inverse norm: independent imported review

**Disposition:** approve the exact finite probability-Haar `L²` norm estimate as a partial gate. The completed inverse operator and the frozen negative `NLA.Statements.SP14.Target` remain open.

I reviewed `EndpointFiniteInverseNorm.lean` at SHA-256 `7b2678fd53cededb71dd8e016b75cc56d2c76fbce1ff387a7ebdedb97ed6ec34` independently of its author. I compared it with the frozen [mathematical and numerical contract](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md), the [independent pre-review](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_INDEPENDENT_PRE_REVIEW.md), and the canonical counterexample manuscript's endpoint-extension lemma. The frozen SP-14 statement and manuscript hashes match that contract (`2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` and `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd`). Its direct dependencies `EndpointFiniteInverseEnergy.lean`, `EndpointFiniteInverseParseval.lean`, and `EndpointInverseHSScalar.lean` also match their reviewed source hashes.

The public theorem is exactly

```lean
theorem endpointFiniteInverseLp_norm_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r) (N : ℕ) :
    ‖endpointFiniteInverseLp r y N‖ ≤
      endpointInverseHSBound r * ‖y‖
```

Here `endpointFiniteInverseLp` is the already audited `Lp ℂ 2` class of the *actual* finite triangular inverse on `AddCircle (2π)` with probability Haar measure, and `endpointInverseHSBound r` is definitionally `1 + 1 / (r - 1 / 2)`. There is no additional upper bound on `r`. The proof combines the exact finite Parseval identity, the audited finite coefficient-energy inequality, and `S_r ≤ B_r²`; it uses positivity to remove squares. In particular, `N=0` is included. I rechecked the contract's rational witnesses `B_(3/4)=5`, `B_(7/8)=11/3`, and the first two nontrivial squared column factors `5/4`, `89/64`.

I compiled the frozen module with pinned Lean 4.33.1 (`lake build NLA.Proofs.SP14.EndpointFiniteInverseNorm`, 3,105 jobs) and independently imported it in `/private/tmp/nla-sp14-norm-independent-audit.lean`. The latter typechecked an exact-signature example, ran `#assert_trust kernel` under LeanCert `kernel`, and printed only `[propext, Classical.choice, Quot.sound]` for the theorem. The source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. The module can be aggregate-imported as this finite gate; no `L²` completion or final counterexample is inferred.
