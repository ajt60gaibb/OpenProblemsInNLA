# TR-14 ordinary and symmetric width chart transport: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import as an exact rank-preserving chart bridge. It does not assert equality of ordinary and symmetric widths or the frozen Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2WidthTransport.lean` | `5a50bb7984b3a9dd034faae43ab088f4ec10880ce37128cad9afd79af1a528a4` |
| Exact chart-transport mathematical contract | `5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322` |
| Independent mathematical pre-review | `0b225faaed0d307e582bc75946b540e872d1fdad927495e27d18f847d0b0ceb2` |
| Audited Hankel-mode identity | `5b700ce0fbd05cfa39f047830b6455dc64cc361acfe3218f667d2af9f09e02c2` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-gl2widthtransport-independent-audit.lean` | `3f16e5bdb087cefdb25ec7f437c97238f610afb3ba1fe482b3c0cc782a83b248` |

The source starts from the audited all-mode multilinear identity and evaluates a tensor on standard basis vectors to recover each frozen tensor entry. Its finite product/sum factorization proves that a decomposable tensor contracts as the product of its mode pairings, and a symmetric summand uses one shared pairing vector in all modes. These identities cover an empty decomposition (`r=0`) and all natural `m,q`.

For the forward chart, `chartFactor` sends a coefficient factor `v` to the vector whose `i`th coordinate is the pairing of `v` with `M_z⁻¹e_i`, where `M_z=chartCoefficientEquiv z q`. This is the ordinary inverse transpose action `(M_z⁻¹)^T v`, with no complex conjugation. The reverse map uses `M_z^T v`. Both forward and reverse proofs give explicit witnesses for the **frozen** `OrdinaryWidth` and `SymmetricWidth` definitions at the same `r`; symmetric scalar coefficients are retained and the same factor map is applied in every mode. The exported conjunction of biconditionals therefore preserves each width predicate separately for arbitrary moments, including zero moments and `r=0`. It does not infer one predicate from the other.

The separate imported audit exited zero under pinned Lean 4.33.1. It checked both factor maps, all four directions, and the combined exact signature; it reran `#assert_trust kernel` and printed only `[propext, Classical.choice, Quot.sound]` for each public width theorem. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

Middle-catalecticant rank transport, symmetric upper constructions, and the arbitrary ordinary-rank lower bound still stand between this chart bridge and the all-width `NLA.Statements.TR14.Target`.
