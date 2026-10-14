# SP-14 finite corrected odd support: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE the frozen contract for implementation, conditional on the separately required final audit of its imported odd-frequency characteristic-polynomial module. This is support and continuity for finite corrected symbols, not the full SP-14 `Target`.

The contract uses the **actual frozen** `FourierCoefficient`, a real interval integral with exponent `exp(−ikt)` and normalization `1/(2π)`. Each constituent is a finite sum of continuous integer circle modes. The positive packet has modes `2m+1` and `2m+3`; the raw negative term `zL(z²)` has modes `1+2(d−m)` for `d:Fin q`; the restoring term `zK_m(z²)` has modes `1−2(m+1+r)` for `0≤r≤m`. Every one is odd, regardless of coefficient values, `q≤m`, or stage separation. Exact orthogonality of the reviewed circle-mode integral therefore gives zero at every even frequency `2p`, including negative `p` and zero. Additivity across finite sums is justified by continuity and interval integrability of both summands; no linearity of a totalized integral for arbitrary functions is assumed.

The dependent family `nv : ∀ j : Fin vCount, Fin(nQ j) → ℂ` retains each packet's exact coefficient count. At `u=vCount=0`, both finite sums vanish and the symbol is exactly `baseExteriorSymbol`. At `q=0`, `negativeL=0` and its restored packet is zero. At `m=0`, `K₀(s)=−s⁻¹`, so its circle contribution has frequency `−1`, still odd. Arbitrary complex coefficients include the source's real correction vectors. The source's `q=3m/8` and order-separation conditions are unnecessary for this parity claim, and the contract does not infer any packet invisibility from parity alone.

Once finite odd support is proved, the jet-coordinate characteristic-polynomial identity follows from the generic theorem under its explicit support premise. It asserts the polynomial shape `X*R(X²−1)` for all odd section sizes, including size one; it does **not** assert that a coefficient of `R` vanishes. The infinite corrected symbol, selection equations, root multiplicities, norm budgets, both nonextensions, empirical measure, and compactly supported test gap remain open.

| Reviewed input | SHA-256 |
| --- | --- |
| **`FINITE_CORRECTED_ODD_SUPPORT_PRE_REVIEW.md`** | **`2c2e5bce752864ca69d1ff9d29935131c86750a0c610e85b72df0fe234004b5d`** |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `PositivePacketInvisibility.lean` | `90df55a41491c60d442df3679d1808c2c77a66d8e66fe8dbffe940151c3c8d1f` |
| Frozen `NegativeRestorationInvisibility.lean` | `318f9d1b2a0af4bf8355aa78afc7440b9c83449b6b2f5de8bd1bc361ac36e476` |
| Frozen `OddFrequencyToeplitzCharpoly.lean` | `aa6de57a4b247b81296d36fb2ed70f47d9c0b1863d0290792f6f3c16b3d4aff5` |

Any changed contract or source bytes reopen this review. The eventual source requires separate exact-signature, LeanCert kernel, and transitive-axiom audits.
