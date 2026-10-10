# TR-14 homogeneous coefficient basis: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen basis module for aggregate import as a partial TR-14 result. It proves no apolar or tensor-rank statement by itself.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2CoefficientBasis.lean` | `548b46a87516484b75022bd5d0d901132ab37762d4991ebb09eeec5b0f509a2f` |
| Independent mathematical pre-review of the apolar chart stage | `8d7c64bdef1741b9f1784b1a7889e742b82af064180e08ee11e29a0d3a011cf2` |
| Prior audited `GL2Homogeneous.lean` | `5d91423c625d687c034b3df7cd14b1a652a707edc4ee436e36d44521baa0f4b7` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit, `/private/tmp/tr14-gl2coefficientbasis-independent-audit.lean` | `d521e11d7156bb7a515f5f1e7fa5cdf4f0db835a04e9db2602cb95d883e971ce` |

`binaryExponent d i` is exactly the two-coordinate exponent pair `(d-i,i)`. The source proves its total degree is `d` and that every degree-`d` exponent pair is uniquely obtained this way; both inverse laws use the two coordinates, so degree zero and both endpoint indices are included. The linear equivalence `binaryFormEquiv d` is a composition of actual linear equivalences: finite functions to finsupp, reindexing by this exponent equivalence, supported monomials to the supported polynomial submodule, and the verified equality with Mathlib's homogeneous submodule. It is therefore both injective and surjective onto genuine homogeneous forms, not an unverified coordinate map.

The single-coordinate theorem identifies each standard vector with exactly `X^(d-i)Y^i`, with no binomial factor. The finite-sum theorem identifies **every** vector with `Σ_i g_i X^(d-i)Y^i`, and the inverse theorem recovers every single coefficient. The multiplication theorem gives `X^(d-i)Y^i · X^(e-j)Y^j = X^(d+e-i-j)Y^(i+j)` with the correct bounded index `i+j`. These are precisely the basis and product facts needed for the next all-shift apolar pairing.

The separate imported audit completed with exit code zero using pinned Lean 4.33.1 and LeanCert `kernel` mode. It checked the public signatures, reran kernel trust assertions on all exported equivalences and key theorems, and printed only `[propext, Classical.choice, Quot.sound]` in the transitive axiom sets. The frozen source contains no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

The moment functional, exact apolar product equivalence, chart apolar transport, normalization, width transport, and the frozen all-width target remain separate. Changed source bytes require a new final review.
