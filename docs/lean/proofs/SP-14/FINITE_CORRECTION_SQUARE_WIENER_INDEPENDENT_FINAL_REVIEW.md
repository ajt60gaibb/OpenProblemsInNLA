# SP-14 finite correction square: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen actual-correction W^(9/8) square gate for aggregate import. It is a part of the finite-background estimate, not the full SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FiniteCorrectionSquareWiener.lean` | `c939eb60f869491c9b897b2246a67c01d36b0109f35d3cca7e26e9b28aeefec8` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-finite-correction-square-wiener-independent-audit.lean` | `426573d81779684096f498c58de26682c3c9454cc3dc955484e5ebb0e667f7bd` |

For the **actual** finite correction `P=P₋+P₊`, the source proves weighted Fourier summability and `W(P)≤W(P₋)+W(P₊)` using audited finite negative and positive Fourier results and the reviewed addition inequality. It expands the literal square as `P²=P·P₋+P·P₊`; both products have summable weighted coefficients and constant-one multiplier bounds. The resulting exact numerical inequality is `W(P²)≤(W(P₋)+W(P₊))²` for all finite coefficient lengths, including zero. The size on the left is the frozen integral-based Wiener size, not a substitute coefficient norm.

The direct pinned Lean 4.33.1 module build passed 2,775 jobs. A separate imported audit checked all four public theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. The remaining base-factor term and full `h−s` bound are separate obligations.
