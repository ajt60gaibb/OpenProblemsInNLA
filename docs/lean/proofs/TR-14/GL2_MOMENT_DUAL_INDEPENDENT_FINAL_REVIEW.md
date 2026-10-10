# TR-14 homogeneous moment dual: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen moment-dual module for aggregate import as a partial TR-14 result. It proves no apolar or tensor-rank transport yet.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2MomentDual.lean` | `09d4126c2c3762fd15f13a026cca8aa085abcfd21bd32627396819bda4ab0de2` |
| Independent mathematical pre-review of the apolar chart stage | `8d7c64bdef1741b9f1784b1a7889e742b82af064180e08ee11e29a0d3a011cf2` |
| Audited `GL2CoefficientBasis.lean` | `548b46a87516484b75022bd5d0d901132ab37762d4991ebb09eeec5b0f509a2f` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit, `/private/tmp/tr14-gl2momentdual-independent-audit.lean` | `b681009a7b8ecee6ade15d1bc5c8639f630e8aa0a9cc42e5dd586664f8008dc8` |

For every `D≥0`, `homogeneousMoment h` is the complex-linear functional `P ↦ Σ_j h_j · coeff_D(P)_j`, using the inverse of the audited genuine homogeneous-form coefficient equivalence. `homogeneousMoment_monomial` identifies its value on `X^(D-j)Y^j` with exactly `h_j`, with no binomial coefficient or conjugation. The two inverse theorems recover every moment vector from its functional and every homogeneous dual from its monomial coordinates. This holds in degree zero as well as positive degrees; the source's associated binomial binary form is deliberately distinct from this dual pairing.

`transformedMoments z h` is the coordinate vector of the already audited inverse-dual chart action. The theorem `homogeneousMoment_transformedMoments` proves the exact functional identity `L_(h^z)=L_h∘φ_D⁻¹` rather than assuming it. The zero equivalences follow from the two coordinate inverse identities and the chart equivalence, so nonzero moments remain nonzero under the explicit chart. The source does not yet prove the map `h↦L_h` as a separately exported linear equivalence, but its values and two inverse identities establish the coordinate bridge needed for the following product-pairing theorem.

The separate imported audit completed with exit code zero under pinned Lean 4.33.1 and LeanCert `kernel` mode. It checked each public type, reran kernel trust assertions, and printed only `[propext, Classical.choice, Quot.sound]` as the transitive axiom set. The frozen source contains no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

The exact `IsApolar ↔ ∀Q L_h(GQ)` theorem, all-degree apolar chart transport, normalization, Hankel mode/width transport, and the frozen all-width target remain open. Changed source bytes require a new final review.
