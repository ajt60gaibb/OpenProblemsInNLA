# MF-03 dense-set cosine product: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source for aggregate import. It proves the exact factorial-series identity and finite-product convergence when `sin(πw)≠0`; integer arguments and the full MF-03 Target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/MF03/CosineDenseProduct.lean` | `0190869c463e7b06c1ced4beec8fdfd1b68481e60a688ff472b27a368e20be28` |
| Exact pre-implementation contract | `ee39fe82fc64a8c365f15b97c7457cb839cce2f05efae918a25f6704763ba98f` |
| Independent mathematical pre-review | `4d1865e46439e7ace030b16de371423f51c5ebac6efdb88f5cb6e52c9c018d30` |
| Separate imported audit `/private/tmp/mf03-cosine-dense-independent-audit.lean` | `2f39c1415bf8dd8ab45f6300242ad4d03bbf1917364387c89c6d94f4929dde1b` |

The source identifies every term of the frozen factorial `waveSeries` at `−(πw)²` with the convergent complex cosine series. For finite products, the parity split of `S_(2N)(2w)` matches every odd factor of `cosinePartialProduct N (−(πw)²)` and every even factor of `S_N(w)`, including the empty product. The pinned Euler sine-product limit includes the leading `πw`; consequently `A_N=2B_N C_N` has the exact double-angle limit. The hypothesis `sin(πw)≠0` permits cancellation at the limit and yields `C_N→cos(πw)`.

The pinned Lean 4.33.1 direct module build passed 8,711 jobs. My separate imported LeanCert audit exited zero, checked both exact public signatures, reran their `#assert_trust kernel` checks, and printed only `[propext, Classical.choice, Quot.sound]` for each. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The all-complex product identity, coefficient transfer, large-order normalized pair existence and bounds, orders at least 16, and full MF-03 Target remain open.
