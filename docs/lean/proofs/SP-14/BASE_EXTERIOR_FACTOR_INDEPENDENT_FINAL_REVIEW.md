# SP-14 normalized exterior boundary factor: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen Gate 1 source for aggregate import. It proves the exact normalized boundary factor identities, without asserting exterior holomorphy or the negative SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/BaseExteriorFactor.lean` | `a8dbc23e8544378ab504ff8130387701fa0270cb2753555c0f05b71057d316dd` |
| Exact factor/background precontract | `351bd895ab5f59accae68ab8f566677045a4fe4f119214356b77f8b5a4518b6a` |
| Independent mathematical pre-review | `c9da91607ffc44fe64f8493068e508ea23312ad8ed30b12a2ad0d8ee76f6394f` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit `/private/tmp/sp14-baseexteriorfactor-independent-audit.lean` | `d5f755aae7c9c67518bd36080c6fc376323be9f280f3b4a6a1b2d66200389248` |

The definition is the exact complex `Circle` series `Σₙ baseCoeff n · s^(−n)`, with the audited half-binomial coefficients and no arbitrary square-root choice. Unit-modulus circle powers reduce the term norms to the already proved summable coefficient norms. The Cauchy product uses the audited coefficient convolution: only degrees zero and one survive, giving `g₀(s)^2=1+s⁻¹` at every circle point, including `s=-1`. The zero identity follows without dividing by `g₀`. Termwise substitution `s=z²` changes each exponent to `−2n`, and multiplication by `z` recovers exactly the existing `1−2n` exterior symbol series. Continuity follows from uniform domination by the coefficient norms.

The pinned Lean 4.33.1 direct module build passed 2,622 jobs. My separate imported audit exited zero, checked the five public signatures, reran `#assert_trust kernel` for each, and printed only `[propext, Classical.choice, Quot.sound]` for the square and symbol factor identities. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The finite Laurent background is Gate 2; exterior holomorphy, Wiener and Sobolev estimates, packet existence, and the original negative Target remain open.
