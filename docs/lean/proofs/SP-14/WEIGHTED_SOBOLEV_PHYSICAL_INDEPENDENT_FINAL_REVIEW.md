# SP-14 weighted Sobolev physical coefficients: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source as a partial physical-space identification for aggregate import. It does not yet provide continuous Sobolev maps or the frozen SP-14 negative target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/WeightedSobolevPhysical.lean` | `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109` |
| Exact mathematical precontract | `194d333896e57d5dc11f638dfcf0646f94fc95bfff9f1fbe0e69353058178df8` |
| Independent preimplementation review | `b504db5cfe1f2df2b3568d4abc6716e229d6f5213db18a8c9e6e056bcea9bc6c` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported LeanCert audit `/private/tmp/sp14-weightedsobolevphysical-independent-audit.lean` | `a38c9135b27beb5dd722ad190c8d48f9dd5bf6c5918371a2ed05fe6d3b8558d0` |

The module uses the complete complex `lp 2` space as a carrier for each real `s`. Its public physical coefficient is exactly `a_n=(n+1)^(-s)y_n`, and its inverse weighted coordinate is `(n+1)^s a_n`. The two pointwise inverse identities hold for every natural index, every real `s`, and arbitrary complex coefficients; the proof uses positivity of `n+1`, so negative indices or a branch choice cannot enter. The exact identity `‖(n+1)^s a_n‖²=(n+1)^(2s)‖a_n‖²` is proved, then summed to give `‖y‖²=∑_n(n+1)^(2s)‖a_n‖²`. The source also constructs both directions of a bijection between the complete carrier and precisely the physical sequences satisfying the weighted-energy summability predicate. Thus the real exponent is not merely a decorative parameter.

This first module exports an ordinary `Equiv`, not yet a formal complex-linear isometric equivalence on a normed physical-sequence subtype. Complex linearity of the coefficient identification is a straightforward coordinate calculation but is not among the audited theorem conclusions. The separately required `H^(s+τ)→H^s` inclusion, degree-`<n` truncation, finite lift, their continuous linearity and norms, and sharp `(q+1)^(-τ)` and `h^τ` inequalities remain open here. No actual background-dependent inverse estimate or counterexample is claimed.

The independent audit imported the compiled source in pinned Lean 4.33.1, checked every exported definition and the five principal theorem signatures, reran `#assert_trust kernel`, and printed exactly `[propext, Classical.choice, Quot.sound]` for each audited theorem and the equivalence. It exited zero. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`. Changed source bytes require a new review.
