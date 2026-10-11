# TR-14 middle catalecticant chart transport: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves exact middle-rank transport and the least-apolar rank theorem in original coordinates. It does not prove equality of ordinary and symmetric tensor widths or the frozen `Target`.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2MiddleRankTransport.lean` | `00d2b76e502b2ddc9f06b9cd0379d39d646399fc15d826f7d549dfc63a2e7b13` |
| Exact GL₂ chart mathematical contract | `5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322` |
| Independent mathematical pre-review | `0b225faaed0d307e582bc75946b540e872d1fdad927495e27d18f847d0b0ceb2` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-gl2middlerank-independent-audit.lean` | `491a84e72b1bb05e2f6199e36254a92d5b0c34feaf0e8af098ae02d20b69b261` |

The matrix has rows `0,…,floor(D/2)` and columns `0,…,ceil(D/2)`, with entry `h_(i+j)`. Its matrix-vector product is exactly the previously audited apolar convolution at degree `ceil(D/2)`; commutation of complex multiplication changes no coefficient or weight. This gives equality of the full kernels, including even, odd, and `D=0`. The already audited invertible coefficient chart carries that kernel to the transformed moment kernel. Rank-nullity, with the same domain dimension on both sides, therefore proves rank equality for every degree and every moment vector.

For a nonzero original moment vector, the source takes **any** supplied nonzero least-degree apolar witness, transports it to a monic chart using the previously audited chart-selection theorem, applies the previously audited normalized middle-rank theorem there, and transports the rank back. No root-at-infinity or uniqueness assumption is added. Its exact result is `rank = r₀` under the explicit least-apolar hypotheses, not a tensor-width equality.

The pinned Lean 4.33.1 direct module build passed 3,045 jobs. My separate imported LeanCert audit exited zero, checked the exported signatures, reran `#assert_trust kernel` on the public bridge and rank theorems, and printed only `[propext, Classical.choice, Quot.sound]` for both rank theorems. A source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, or `native_decide` escape. Changed source bytes require a new review.

The two symmetric upper constructions and the arbitrary ordinary-rank lower bound remain open before `NLA.Statements.TR14.Target` can be proved.
