# TR-14 homogeneous GL₂ chart transport: independent mathematical pre-review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `GL2_CHART_TRANSPORT_PRE_REVIEW.md` as the exact chart bridge required before applying normalized quotient and middle-rank results to arbitrary original moments. This is a pre-implementation review, not a Lean proof or the all-width `TR14.Target`.

I compared the contract with canonical `solution.tex` §2 and the frozen zero-based Hankel definitions. A degree-`D` moment vector is exactly the dual functional taking `X^(D−j)Y^j` to `h_j`; no binomial factor is part of this pairing. With `φ_{T,d}P=P∘T` and `L_{h'}=L_h∘φ_{T,D}^{−1}`, multiplicativity gives `L_{h'}((φ_{T,d}P)(φ_{T,D−d}Q))=L_h(PQ)` for every split. The inverse-dual orientation is correct. The exact apolar convolution is equivalent to annihilating all products `GQ`, because the monomial basis of `V_{D−d}` covers every shift `0,…,D−d`. Thus invertible `φ_{T,d}` carries the complete apolar kernel in **every** degree `d≤D`, preserving nonzero moments, least degree, and kernel dimensions.

A nonzero homogeneous binary form has a nonzero dehomogenization `G(1,z)`; otherwise all its coefficients vanish. Since `ℂ` is infinite, some `z` gives a nonzero value. The displayed matrix `[[0,1],[1,z]]` has determinant `−1` and sends `(0,1)` to `(1,z)`, so the transformed last coefficient is nonzero. Scaling makes the affine polynomial monic of exact least degree without assuming no infinity root, squarefreeness, or uniqueness of the balanced apolar form. This includes `r₀=1` and `D=1`; the zero vector stays a separate endpoint.

For each mode, `M_T` is the coefficient matrix of the invertible degree-`q` substitution. The exact multilinear Hankel identity comes from multiplying `m` mode polynomials and reading their zero-based summed exponent; every product coefficient is counted once by the tensor sum. The contract correctly yields `H_{h'}(M_Tu_1,…,M_Tu_m)=H_h(u_1,…,u_m)`. On coordinate tensor factors the resulting action is ordinary inverse transpose, with its inverse the ordinary transpose; no conjugate transpose appears. Consequently both ordinary and symmetric widths are preserved **separately** at each `r`, including `r=0`. The middle pairing gives `M_{T,a}^T C_{h'}M_{T,b}=C_h`, preserving rank. As the contract emphasizes, this rank relation alone cannot transport the least apolar degree; the all-degree kernel theorem must be proved before applying the normalized middle-rank result.

The proposed Lean signatures are API sketches. Implementation must prove the coefficient isomorphisms, multiplication law, dual inverse law, all-degree apolar transport, nonzero/least-degree preservation, mode identity, and the actual frozen width equivalences. It may split these into modules, but no chart, monicity, genericity, or selected-width premise may be added to `NLA.Statements.TR14.Target`. Local CRT and arbitrary ordinary-rank lower bounds remain separate.

| Reviewed input | SHA-256 |
| --- | --- |
| **`GL2_CHART_TRANSPORT_PRE_REVIEW.md`** | **`5ae018eb2b872a83e3a22bb0e1a77dd2d1db8d5944f8c13319a977c2b4929322`** |
| Canonical `tensor-computations/TR-14/README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `lean-statements/NLA/Proofs/TR14/FrobeniusMinimal.lean` | `dca235b899ba5729e5bdfb50986e55836989c2736b133ee6e2b4a7f428dee29e` |
| Audited `lean-statements/NLA/Proofs/TR14/MiddleCatalecticant.lean` | `2ddbf89822f72c4cbc5a2cd6935adbbab49239476943275ac4a5b2853be9d8a1` |

Changed contract bytes reopen this review. Every future frozen Lean source needs a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom review.
