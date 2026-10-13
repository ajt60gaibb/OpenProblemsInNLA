# SP-14 finite inverse tail: independent imported review

**Disposition:** approve the exact finite probability-Haar `L²` tail inequality as a partial gate. Completing the inverse on all weighted inputs and proving the frozen negative `NLA.Statements.SP14.Target` remain open.

I reviewed `EndpointFiniteInverseTail.lean` at SHA-256 `50c51acec1c52097c164bff3ef95d161b9fc49cfb30fc913b56df8bc4e21fe15` independently of its author against the source-locked [Parseval/completion contract](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_PRE_REVIEW.md) and [independent pre-review](ENDPOINT_INVERSE_PARSEVAL_COMPLETION_INDEPENDENT_PRE_REVIEW.md). The theorem uses the previously audited actual finite inverse, literal weighted Sobolev truncation, and the sufficient constant `endpointInverseHSBound r = 1 + 1/(r - 1/2)` for every `r>1/2`. It adds no upper restriction on `r`.

The public signature exactly matches the approved contract:

```lean
theorem endpointFiniteInverseLp_tail_le (r : ℝ)
    (hrHalf : (1 / 2 : ℝ) < r) (y : SobolevCoeff r)
    (M N : ℕ) (hMN : M ≤ N) :
    ‖endpointFiniteInverseLp r y N - endpointFiniteInverseLp r y M‖ ≤
      endpointInverseHSBound r * ‖y - sobolevTruncation r M y‖
```

The private subtraction lemma proves finite inverse linearity at the pointwise continuous-function level and transports it to the probability-Haar `Lp` class. The proof then replaces the `M`-length output by the `N`-length output of the literal `M`-truncated input using the independently audited finite truncation identity, and applies the finite norm bound to the **actual** input tail. Thus it covers `M=0` and `M=N` without weakening the norm or increasing the coefficient.

I independently imported the frozen module in `/private/tmp/nla-sp14-tail-independent-audit.lean`, typechecked an exact-signature example, and ran `#assert_trust kernel` under LeanCert `kernel`. Pinned Lean 4.33.1 exited zero; `#print axioms` reported only `[propext, Classical.choice, Quot.sound]`. The source has no `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`. The split aggregate `lake build NLA.Proofs` passed 3,136 jobs after import. Aggregate import is approved as this finite tail bound only.
