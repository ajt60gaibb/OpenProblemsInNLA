# SP-14 weighted Sobolev sequences: independent mathematical and numerical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract for incremental Lean implementation. This is the concrete geometry required by the abstract oversampling lemma, not the background inverse estimates or `NLA.Statements.SP14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `WEIGHTED_SOBOLEV_SEQUENCE_PRE_REVIEW.md` | `194d333896e57d5dc11f638dfcf0646f94fc95bfff9f1fbe0e69353058178df8` |
| Canonical `counterexample.tex`, “Oversampling from two Sobolev bounds” | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Audited abstract `SobolevOversampling.lean` | `fd9b5a433847dc8392070752a97244bebeedde08d4d7f7a198e24d64f6f27d77` |

For every real `s`, the proposed physical coefficient sequence `a_n=(n+1)^(-s)y_n` on a complete complex `ℓ²` carrier has exactly `∑(n+1)^(2s)|a_n|²=∑|y_n|²`. Every factor is positive because `n+1>0`, so the inverse coordinate map is `y_n=(n+1)^s a_n`, including negative `s` and `n=0`. Requiring both inverse maps and the norm-square identity prevents an unweighted `ℓ²` type with a decorative `s` parameter from substituting for the source's `H^s`.

With `r=s+τ` and `τ>0`, inclusion that preserves physical coefficients becomes the diagonal `ℓ²` multiplier `(n+1)^(-τ)`. It has operator norm at most one. The literal degree-`<n` truncation is a coordinatewise `if k<n` projector with norm at most one and `P_0=0`. The lift from `H^s` to `H^r` is the finite-support multiplier `(k+1)^τ` for `k<h`, zero otherwise; hence it is bounded, `L_0=0`, and inclusion after lift is exactly `P_h` in every coordinate. These formulas include all coefficients, including the last retained one `k=h−1`.

For the tail, `k≥q` implies `k+1≥q+1`; since `τ>0`, `(k+1)^(-2τ)≤(q+1)^(-2τ)`. Comparing nonnegative squared terms and then taking square roots gives `‖(I-P_q)ιx‖_s≤(q+1)^(-τ)‖x‖_r`. For the lift, `k<h` implies `k+1≤h` when `h>0`, so `(k+1)^(2τ)≤h^(2τ)` and `‖L_hy‖_r≤h^τ‖P_hy‖_s`. At `h=0`, both operators vanish and `0^τ=0`; at `q=0`, the tail constant is one. The `q+1` and `h` factors match the canonical source exactly.

I independently checked the contract's finite numerical example with exact rational arithmetic: for `s=0,τ=1,a=(1,2,3)`, the squared norms are `14` and `98`; at `h=2`, the lift has squared norm `17≤20=4‖P_2a‖_0²`; at `q=2`, the tail has squared norm `9≤98/9`. The single `k=q=2` mode gives equality `9=81/9`, and the single `k=h−1=1` mode gives equality `16=4·4`. These checks confirm the sharp index shifts; the Lean proof must cover all summable sequences.

The implementation may be divided into audited modules. Every exported coordinate and norm theorem must refer to the physical coefficient map and the complete normed spaces, not merely to a finite vector or an abstract space with the desired inequalities assumed. The actual background-dependent compatible inverses, their bounds, the nonlinear construction, and the frozen negative target remain open. A frozen Lean source will require a separate signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit.
