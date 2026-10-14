# SP-14 actual contact product Wiener bound: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves the first exact weighted product estimate for the actual contact-corrected base factor, not the complete SP-14 counterexample.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/ActualNegativeWienerBound.lean` | `88ecdcd0a7431762eec862ea623a2425884b118ff2fcbc71486159384317d224` |
| Exact finite-product contract | `96e380a841054940a4ac07ffbee67dcef4eac45efac75979fcf991e5c82bad9d` |
| Independent mathematical pre-review | `6a27de7fa30a4ad287568928efcb38870045816b66849b83b50042a9c45b20d4` |
| Separate imported audit `/private/tmp/sp14-actual-negative-wiener-bound-independent-audit.lean` | `c92b975a103b05ffb14e9f3a05172d49bd00f6ac0bed38f843ba53c153b797ab` |

From the actual endpoint equation `P₋(-1)=0`, the source obtains the previously proved same-length real quotient `q`, its zero first coefficient, and the pointwise factorization `P₋=(1+s)Q₋`. The exact identity `baseExteriorFactor*(1+s)=regularizedBaseFactor` rewrites the actual product as `regularizedBaseFactor*Q₋`. It then applies the independently audited literal `9/8`-weighted summability of the regularized factor and the constant-one finite-negative-Laurent multiplier theorem. The exported conclusion retains the actual `FourierCoefficient` interval integral, the concrete product, the quotient witness, and its finite Wiener size. It includes empty and one-term corrections.

The pinned Lean 4.33.1 direct module build passed 2,770 jobs. My separate imported LeanCert audit exited zero, checked the full public existential/conjunction signature, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The remaining smallness estimates, compatible background inverses, infinite symbol, two-sided nonextension, and full SP-14 Target remain open.
