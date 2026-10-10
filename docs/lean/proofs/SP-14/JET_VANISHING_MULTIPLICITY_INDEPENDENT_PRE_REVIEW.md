# SP-14 jet vanishing to root multiplicity: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE the frozen contract for conditional finite-polynomial implementation. It does not solve a jet system or the SP-14 `Target`.

`JetVanishing a m h` uses the **ordinary coefficients** `R.coeff d=0` for every `d<h` in the source's exact coordinate `t=w²−1`. For any polynomial over `ℂ`, this is equivalent to `X^h ∣ R`; no derivative normalization or analytic Taylor approximation is involved. The reviewed odd-frequency theorem, under its explicit actual-Fourier support premise, gives `χ(w)=w R(w²−1)`. Composing a polynomial divisibility witness by `X²−1` proves `(X²−1)^h ∣ χ` without dividing by `w` at any value. Since `X²−1=(X−1)(X+1)`, both `(X−1)^h` and `(X+1)^h` divide the nonzero monic characteristic polynomial. Therefore its root **multiset** contains at least `h` copies of each `1` and `−1`, matching the frozen `Empirical` definition's algebraic multiplicity. A statement only about `IsRoot` or geometric eigenspaces would be too weak.

The theorem's `h≤m` covers the source's intended first-jet range. At `h=0`, all polynomial and multiset inequalities are trivial. At `m=0`, that bound forces `h=0`; the generic odd-support `1×1` characteristic polynomial is `X`. The unrestricted helper `JetVanishing → X^h∣R` remains valid even if `h>m`; for monic degree-`m` `R`, its premise is then impossible. The finite corrected-symbol corollary must retain both the actual dependent `Fin` packet family and an **explicit** `hJet` hypothesis. The source's `h=⌊θm⌋` and its exact θ are a later numerical-selection obligation, not established by this implication.

| Reviewed input | SHA-256 |
| --- | --- |
| **`JET_VANISHING_MULTIPLICITY_PRE_REVIEW.md`** | **`6af78ee310030425379eb0d15081fa1e6312d7787a8f3cbd1405f1f6cb9a432c`** |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Reviewed `OddFrequencyToeplitzCharpoly.lean` | `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5` |

Changed source or contract bytes reopen this review. The future Lean theorem requires its own exact-signature, source-hash, imported LeanCert kernel, and axiom audit.
