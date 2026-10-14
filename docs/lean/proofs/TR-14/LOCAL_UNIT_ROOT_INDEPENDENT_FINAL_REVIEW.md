# TR-14 local Frobenius unit and nth root: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen local algebra source for aggregate import. It proves the exact nonzero coefficient and finite root gates, without CRT, width construction, or the full TR-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/LocalUnitRoot.lean` | `ce623be5bde47e2e60c5198c31ac3215ed061d7b2a8d7d278e415390f9b1dc28` |
| Exact local algebra contract | `c5797947009882f77bacc12d3a3f641178a38a6aa134ffc842aba9cb9ecab37b` |
| Independent mathematical pre-review | `a1956c229aaa16e4d157e8eb25cd33db09dcd495eae45babb7b96bbe9a6072cf` |
| Audited preceding local top-coefficient source | `0803a7a5c625b364527b4cbbcbba825d6dd410c81ef648018e18ee4f5cfc3275` |
| Separate imported audit `/private/tmp/tr14-localunitroot-independent-audit.lean` | `7b4d81d2e158b1c5fab707c8c0e55f68a2d52aa890f155bc16c0096534d04096` |

The Frobenius implication uses the actual `ℂ[z]/(z^ℓ)` quotient for every `ℓ>0`: if the reversed element's constant coefficient vanished, its product with the nonzero class `z^(ℓ−1)` would be zero. The reviewed representation `Λ(a)=top(u a)` would then put that class in the left radical, contradicting the supplied genuine nondegeneracy. This includes `ℓ=1`.

For any class with zero constant coefficient, the source obtains a polynomial representative divisible by `X`; `z^ℓ=0` makes the class nilpotent. For `u₀≠0` and `m>0`, algebraic closedness gives a nonzero scalar `ρ` with `ρ^m=u₀`. In the polynomial `P(X)=X^m−u`, `P(ρ)` is nilpotent and `P'(ρ)=mρ^(m−1)` is a unit. Mathlib's nilpotent Newton lifting supplies an exact root in the finite quotient. This is an algebraic existence theorem, with no analytic branch or extra genericity assumption.

The pinned Lean 4.33.1 direct module build passed 3,419 jobs. My separate imported LeanCert audit exited zero, checked the precise positive-length, positive-exponent and nonzero-constant hypotheses, reran all three `#assert_trust kernel` checks, and printed only `[propext, Classical.choice, Quot.sound]` for each. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The local Fourier decomposition, global CRT transfer, symmetric width upper construction, arbitrary ordinary lower bound, and full TR-14 Target remain open.
