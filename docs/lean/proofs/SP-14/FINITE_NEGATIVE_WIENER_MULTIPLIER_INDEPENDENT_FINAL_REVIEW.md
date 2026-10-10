# SP-14 finite negative Laurent multiplier: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen generic multiplier module for aggregate import. The endpoint-derived `g₀P₋` specialization and full SP-14 negative Target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FiniteNegativeWienerMultiplier.lean` | `dbdb6f032244fff2108adcabb8bb40dff1602f0cd59969ccc1635b4ec600d858` |
| Exact finite-product contract | `96e380a841054940a4ac07ffbee67dcef4eac45efac75979fcf991e5c82bad9d` |
| Independent mathematical pre-review | `6a27de7fa30a4ad287568928efcb38870045816b66849b83b50042a9c45b20d4` |
| Separate imported audit `/private/tmp/sp14-finite-negative-multiplier-independent-audit.lean` | `0beff8a53d86081502e88f61034f61ec66621e3006d802862a67a23861e4de5e` |

The source proves the exact Fourier shift of a continuous function times each negative circle monomial using the frozen real-interval integral, then sums over the finite quotient. The shift has the required plus `j+1` sign. The literal `9/8` weight satisfies `w(k) ≤ w(k+j+1)w(-(j+1))` by integer absolute-value triangle inequality and positive real powers. The pointwise triangle bound and finite sum over `j` yield weighted summability. Reindexing the bilateral integer sum gives the exact constant-one bound by `weightedWienerSize f * finiteNegativeWienerSize u q`, including the empty finite sum. There is no abstract Fourier surrogate or altered weight.

The pinned Lean 4.33.1 direct module build passed 2,769 jobs. My separate imported LeanCert audit exited zero, checked both public signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The contact-derived product bound, remaining quantitative estimates, background inverse, and full SP-14 Target remain open.
