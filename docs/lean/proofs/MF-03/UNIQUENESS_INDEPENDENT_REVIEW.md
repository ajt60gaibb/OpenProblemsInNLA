# MF-03 normalized-rational uniqueness: independent partial-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `Uniqueness.lean` as a kernel-checked theorem that **any two normalized diagonal Padé pairs of the same order have equal cross products**. This proves uniqueness of the represented rational function, conditional on pairs being given. It does **not** prove pair existence, equality of unreduced polynomial pairs, reducedness, or the full MF-03 Target.

The sole public result, `NLA.Proofs.MF03.normalized_cross_product_eq`, takes an arbitrary natural `m`, arbitrary complex polynomials `P₁,Q₁,P₂,Q₂`, and only `NormalizedPadeRepresentation m P₁ Q₁` and `NormalizedPadeRepresentation m P₂ Q₂`. Its exact conclusion is `P₁*Q₂=P₂*Q₁`. No `IsCoprime` or existence hypothesis is hidden. The normalized representation itself includes degree bounds at most `m`, `Q.eval 0=1`, and the Padé coefficient equation for **every** `j≤2m` inclusive. The theorem works even at `m=0`; the Target's `m≥1` range is contained in it.

The private `waveSeries` is the **formal** complex power series with coefficient `1/(2j)!`. The private bridge expands the product coefficient as the finite antidiagonal convolution and rewrites it to the target's exact sum `Σ_{i=0}^j Q.coeff i/(2(j−i))! = P.coeff j`. This does not assume convergence of `cosh(√z)` or substitute sampled function values for the Taylor equations; formal coefficients alone suffice for uniqueness. If two series agree through order `2m`, multiplication by another series preserves agreement through any `j≤2m` because every contributing left coefficient has index at most `j`. Commutativity of complex power series then gives equality of the coefficients of `P₁Q₂` and `P₂Q₁` for each `j≤2m`.

The degree calculation is exact: `natDegree(P₁Q₂)≤natDegree P₁+natDegree Q₂≤2m`, and likewise for `P₂Q₁`. Polynomial extensionality up to degree `2m` turns the coefficient agreement into full polynomial equality. Since each normalized `Q` has `Q(0)=1`, neither denominator is the zero polynomial, so this cross-product identity means the two quotients agree as rational functions. It does **not** force `P₁=P₂` and `Q₁=Q₂` without reduction or another argument. To use this lemma for the Target's **every reduced pair** clause, a later proof must still construct reduced pairs, prove suitable cancellation/associate-denominator transport, establish their disk nonvanishing and error bound, and handle every order.

I ran `lake build NLA.Proofs.MF03.Uniqueness`, direct `lake env lean NLA/Proofs/MF03/Uniqueness.lean`, and a separate audit importing the theorem. All exited zero with pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The independent audit verified that the export is a `.thmInfo` proof constant and passed `#assert_trust kernel`; its transitive axiom print was exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| **`NLA/Proofs/MF03/Uniqueness.lean`** | **`c781644e76a6143535a45862263e6776ee1257ff6ac2d69eed328dd63f73daa5`** |
| `STATEMENT_REVIEW.md` | `7c7d7c8de42fdf16aff0365dbcaf89586fdf87cd612c6ebab46cfa3b51e0ab41` |
| `STATEMENT_INDEPENDENT_REVIEW.md` | `dff7af4c1fc3b352ef9afbaf422bf644cb77118297b81c71b6793baf080ef2e5` |
| `NUMERICAL_TARGETS.md` | `7330918bbef9002e38a2d38cd1b019d1170a707e3b8c1e4dfcb18e9b4133dd28` |
| Manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56cfb5abf542a18ff36247b` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/mf03-uniqueness-independent-audit.lean` | `7f87add66b8270febbcc54ee84dbb141e0a5a3eb122f769f6de78fe5e0da9550` |

Any changed mathematical source bytes require renewed review of the affected claim.
