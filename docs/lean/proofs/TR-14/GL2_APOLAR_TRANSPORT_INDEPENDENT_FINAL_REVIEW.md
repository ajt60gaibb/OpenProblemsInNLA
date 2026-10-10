# TR-14 all-degree apolar chart transport: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen transport module for aggregate import as a partial TR-14 result. It does not prove chart normalization, Hankel-width preservation, or the frozen all-width target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| Independent mathematical pre-review | `8d7c64bdef1741b9f1784b1a7889e742b82af064180e08ee11e29a0d3a011cf2` |
| Audited `GL2ApolarPairing.lean` | `81be7d13c6df0ef5e28e135f785c344498e4fc4dd88ab5f5963e38adf9681cb5` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit, `/private/tmp/tr14-gl2apolartransport-independent-audit.lean` | `13ff371065f7095a0e6acd3328e4d96f09311b972732eed29b7b249aeb995467` |

`transportedApolarVector z d` takes the genuine homogeneous form of a coefficient vector, applies the audited forward chart substitution `(X,Y)↦(Y,X+zY)`, and returns its exact zero-based coordinates. `chartCoefficientEquiv` proves this is a complex-linear equivalence in **every** degree, including zero. The product pairing theorem applies the inverse-dual moment functional to the product of both forward-transformed forms and obtains the original functional on the original product, for every split `d+(D−d)=D`.

The public `apolar_iff_chart_apolar` theorem combines that product identity with the independently audited characterization of apolarity as annihilation of **all** complementary products. In its forward direction, every transformed test form is the image of some old test form because the degree-`D−d` chart map is surjective; in its reverse direction, it tests the forward image of each old form. Therefore it preserves every frozen convolution equation for every `d≤D`, without a monic, nonzero, or selected-degree premise. The source also proves `g^z=0 ↔ g=0`, equality of the transformed degree-`d` apolar kernel with the image of the original kernel, and equivalence of the existence of nonzero apolar vectors in every degree. Together with the separately proved `h^z=0 ↔ h=0`, the latter is the exact predicate needed to transport a least degree, although a dedicated exported least-degree equality theorem is still to be written before the normalized rank bridge uses it.

The separate imported audit completed with exit code zero under pinned Lean 4.33.1 and LeanCert `kernel` mode. It checked every public signature, reran kernel trust assertions for the coefficient equivalence, pairing, all-degree apolar equivalence, kernel image, and nonzero-degree theorem, and printed only `[propext, Classical.choice, Quot.sound]` as their transitive axiom sets. The frozen source contains no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

The coefficient transport is an explicit invertible chart, not an arbitrary-`GL₂` API. Choosing a chart with nonzero last coefficient, scaling to a monic least apolar polynomial, original-coordinate catalecticant rank, Hankel mode and width transport, arbitrary ordinary-to-symmetric rank bounds, and `TR14.Target` remain open. Changed source bytes require a new final review.
