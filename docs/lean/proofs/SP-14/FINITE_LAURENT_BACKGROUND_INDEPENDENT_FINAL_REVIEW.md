# SP-14 finite real Laurent background: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the revised frozen Gate 2 source for aggregate import. It gives the source's exact finite boundary algebra and contact identities, not its analytic bounds or negative Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FiniteLaurentBackground.lean` | `21ddde26cfbbfec236f7c9ddc3b212702baa56c0ceef333e9289f09f5a052e7b` |
| Exact factor/background precontract | `351bd895ab5f59accae68ab8f566677045a4fe4f119214356b77f8b5a4518b6a` |
| Independent mathematical pre-review | `c9da91607ffc44fe64f8493068e508ea23312ad8ed30b12a2ad0d8ee76f6394f` |
| Audited boundary factor | `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit `/private/tmp/sp14-finitelaurent-independent-audit.lean` | `3b1abd683451401b98da0b52713e66048cfc2ba0228735fab7f707920dce2793` |

The definitions use real coefficients and exactly the strict powers `−(j+1)` and `+(j+1)`, with no constant correction. The public boundary functions are `P₋`, `P₊`, `P=P₋+P₊`, `g=g₀+P`, `h=sg²−1`, and `a(z)=zg(z²)`; all have continuous circle maps. Expanding the square with the audited `g₀²=1+s⁻¹` proves the exact identity `h−s=2s g₀P+sP²`. The symbol identity distributes `z` and uses the audited base-symbol factor, with no sign or frequency shift. The `u=v=0` theorems recover `g₀`, `h(s)=s`, and `a₀` pointwise.

The contact theorems require **separate** values `P₋(-1)=0` and `P₊(-1)=0`, as in the source, and conclude `g(-1)=0`, `h(-1)=-1`. The revised source also proves the nonempty exact check for all real `t,r`: the two negative coefficients `(t,t)` yield `t((-1)^(-1)+(-1)^(-2))=0`, the two positive coefficients `(r,r)` yield `r((-1)+(-1)^2)=0`, and the curve has the required contact. Empty sums and all finite lengths are covered.

The pinned Lean 4.33.1 direct module build passed, and my separate imported LeanCert audit exited zero. It checked all definitions and public signatures, reran `#assert_trust kernel` on the main identities and endpoint cases, and printed only `[propext, Classical.choice, Quot.sound]` for the deviation, symbol, and nonempty-contact theorems. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The source's strict Wiener smallness, exterior holomorphy, conformal map, Sobolev inverse bounds, nonlinear packet construction, two-sided nonextension, and final negative Target remain open.
