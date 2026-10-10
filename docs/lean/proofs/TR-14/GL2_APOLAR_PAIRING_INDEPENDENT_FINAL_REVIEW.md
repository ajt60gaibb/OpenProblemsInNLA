# TR-14 exact apolar product pairing: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen apolar product module for aggregate import as a partial TR-14 result. It does not yet transport apolarity between charts or prove any width claim.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2ApolarPairing.lean` | `81be7d13c6df0ef5e28e135f785c344498e4fc4dd88ab5f5963e38adf9681cb5` |
| Independent mathematical pre-review of the apolar chart stage | `8d7c64bdef1741b9f1784b1a7889e742b82af064180e08ee11e29a0d3a011cf2` |
| Audited `GL2MomentDual.lean` | `09d4126c2c3762fd15f13a026cca8aa085abcfd21bd32627396819bda4ab0de2` |
| Audited `ApolarMinimal.lean` | `0e98ae3b414d2130bebe7470a25c7c8b3e422225b5581ae4b93d036f39f520d9` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit, `/private/tmp/tr14-gl2apolarpairing-independent-audit.lean` | `2344576305aa90cba2c0e8152d9fa55074d8276262d3463f2fc04256a3a6718b` |

For every `d≤D`, `binaryProductAt` multiplies a genuine degree-`d` homogeneous form by a genuine degree-`D−d` form and returns degree `D`; the proof uses exactly `d+(D−d)=D`. On the canonical monomials, the product has index `i+j`, with its Fin bound proved from both source index bounds. Consequently `homogeneousMoment_product_monomial` is exactly the frozen zero-based apolar convolution `Σ_i g_i h_(i+j)` for **every** shift `j:Fin(D−d+1)`; no binomial coefficient, truncation, or leading-coefficient premise appears.

The public `apolar_iff_product_annihilation` theorem has no nonzero, monic, minimal-degree, or genericity hypothesis. The forward proof expands an arbitrary complementary test form in the complete audited basis and uses every frozen apolar equation. The reverse proof tests each individual complementary monomial to recover every equation, including `j=0` and `j=D−d`. Because only `d≤D` is assumed, it also covers `D=0`, `d=0`, `d=D`, `D=1`, and balanced degrees. This is the exact source meaning of `I_d` for the degrees used in the main theorem.

The separate imported audit completed with exit code zero under pinned Lean 4.33.1 and LeanCert `kernel` mode. It checked the public types, reran the kernel trust assertions, and printed only `[propext, Classical.choice, Quot.sound]` as the transitive axiom set. The frozen source contains no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

All-degree chart apolarity, least-degree preservation, normalization, Hankel mode/width transport, and the frozen all-width target remain separate obligations. Changed source bytes require a new final review.
