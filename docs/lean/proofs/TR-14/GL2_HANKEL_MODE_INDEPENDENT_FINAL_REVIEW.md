# TR-14 exact Hankel mode pairing and chart identity: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen module for aggregate import as a partial TR-14 result. It does not yet prove width or middle-rank invariance, or the frozen Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2HankelMode.lean` | `5b700ce0fbd05cfa39f047830b6455dc64cc361acfe3218f667d2af9f09e02c2` |
| Exact GL₂ chart-transport precontract | `5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322` |
| Independent mathematical pre-review | `0b225faaed0d307e582bc75946b540e872d1fdad927495e27d18f847d0b0ceb2` |
| Audited coefficient basis and inverse-dual moment modules | `548b46a87516484b75022bd5d0d901132ab37762d4991ebb09eeec5b0f509a2f`; `09d4126c2c3762fd15f13a026cca8aa085abcfd21bd32627396819bda4ab0de2` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-gl2hankelmode-independent-audit.lean` | `9d4ff3f2aa607e83dfa2d893096ecc5b9dc657193aaa5904c5f075b59727e5c2` |

For arbitrary natural `m,q`, the source constructs the product of `m` genuine degree-`q` homogeneous binary forms and proves its exact expansion over all zero-based multi-indices. The coefficient of each tuple is `∏_k u_k(i_k)` on the monomial indexed by `∑_k i_k`, with no multinomial factor. The definition uses the frozen `HankelIndex` and is valid even for empty modes. Pairing this expansion with the audited degree-`mq` homogeneous moment functional gives exactly the multilinear contraction of the frozen Hankel tensor.

The explicit substitution distributes across all `m` factors, and the coefficient chart equivalence is applied identically in every mode. The inverse-dual moment relation therefore yields the exported equality

`H_(transformedMoments z h)(chartCoefficientEquiv z q · u₁,…,chartCoefficientEquiv z q · u_m) = H_h(u₁,…,u_m)`

as an exact finite coefficient-sum statement for every `z,m,q,h,u`. This has the correct inverse-dual orientation and no conjugate transpose or hidden mode permutation. The source does not infer any ordinary/symmetric rank statement from this identity alone.

The independent imported audit exited zero in pinned Lean 4.33.1, checked all six public definitions/theorems, reran `#assert_trust kernel` for the four substantive theorems, and printed only `[propext, Classical.choice, Quot.sound]` for each. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`. Changed source bytes require a new review.

The next proof must derive the actual frozen OrdinaryWidth and SymmetricWidth equivalences for every width, including zero, by transporting decomposable factors with the inverse transpose map. Middle-catalecticant rank transport and the full all-width equality remain separate obligations.
