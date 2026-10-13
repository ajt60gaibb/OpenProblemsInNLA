# TR-14 monic chart normalization: independent mathematical pre-review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen contract for Lean implementation in audited stages. This review does not assert a width theorem or `NLA.Statements.TR14.Target`.

| Reviewed input | SHA-256 |
| --- | --- |
| `GL2_CHART_NORMALIZATION_PRE_REVIEW.md` | `8d1c179386d1631fbdbd231db4a9b9b9db5d85043ad405fe24d2a3afadcf76e7` |
| Canonical `tensor-computations/TR-14/solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Audited `GL2ApolarTransport.lean` | `8e75a3257801d3738bb0dad87a4dbdab5a614e84449c6874b6f6ac418d814c3b` |
| Audited `NormalizedQuotient.lean` | `3c6809e84eb522ad82c28f49245b80ef6da7da84cd201f46f4cbfb54a363a54d` |

The dehomogenization `p_g(t)=Σ_(i=0)^d g_i t^i` has the exact coefficients of the audited complete homogeneous basis. In particular a nonzero vector gives a nonzero polynomial even when `g_d=0`, because **every** coefficient is recovered. Over the infinite field `ℂ`, a nonzero polynomial is nonzero at some `z`; this choice is existential and requires no numerical root computation. The argument includes the constant form at `d=0`.

For the audited substitution `T_z(X,Y)=(Y,X+zY)`, evaluating the transformed form at `(0,1)` gives the old form at `(1,z)`, exactly `p_g(z)`. Since a homogeneous degree-`d` form evaluated at `(0,1)` equals its `Y^d` coefficient, the proposed identity `(g^z)_d=p_g(z)` has the correct last index and orientation, including `d=0`. As an independent concrete check, `G=X` at `d=1` has original vector `(1,0)` and becomes `Y`, so its new last coefficient is `1=p_g(z)` for every `z`. At `d=2`, the last coefficient of `g₀Y²+g₁Y(X+zY)+g₂(X+zY)²` is `g₀+g₁z+g₂z²`, again `p_g(z)` with no binomial rescaling.

With `a=(g^z)_d≠0`, scaling by `a⁻¹` sets the last coefficient to one. The audited apolar map is complex-linear, so scalar multiplication preserves its kernel. The affine polynomial of the scaled vector has coefficient one at degree `d` and no coefficient above `d`, hence is monic with `natDegree=d` exactly; both properties are needed by the normalized quotient and Frobenius theorems. This avoids inferring exact degree from an upper bound alone.

The source witness assumptions include **every** lower apolar kernel, not only the immediately preceding degree. The audited inverse-dual chart theorem identifies the transformed kernel with the image of each original kernel, so every lower transformed kernel remains zero. The transformed moment vector stays nonzero by the audited dual equivalence. The proof works for any chosen nonzero least form, including the balanced two-dimensional least kernel and an initial infinity root; it makes no uniqueness claim. The zero moment vector remains a separate frozen-target case. An exported theorem must retain all these conclusions and may not add a prior monic-chart premise.

The implementation may split polynomial dehomogenization, the last-coefficient identity, scalar normalization, and the final witness package. Each frozen Lean source requires a separate exact-signature, proof-escape, imported LeanCert kernel, and transitive-axiom audit before aggregate import. Changed contract bytes reopen this review.
