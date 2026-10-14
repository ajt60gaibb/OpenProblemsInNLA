# TR-14 chosen least-apolar chart normalization: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen module for aggregate import as a partial TR-14 theorem. The frozen tensor-width target is not proved.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/TR14/GL2ChartNormalize.lean` | `4b212d23011807f0f9e29803305683a24bb9a4f4e7e1aef7fa63f46d87f35bde` |
| Exact chart-normalization precontract | `8d1c179386d1631fbdbd231db4a9b9b9db5d85043ad405fe24d2a3afadcf76e7` |
| Independent mathematical pre-review | `47bad244d52518460cb481cf9e02ed17628cc3c1b702b3002fb0411878c9559e` |
| Audited dehomogenization source | `3de97ab8ba4f9733fe6e876808f9d6ea9c0e1d33ff9ddea9219baf09aeda9af5` |
| Frozen `NLA.Statements.TR14` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Separate imported audit `/private/tmp/tr14-gl2chartnormalize-independent-audit.lean` | `e9c030347cfc9fc3bc7cca0fceb3c1cb79213657c0230c19a6fa2cf9eab61e3f` |

The theorem starts with an arbitrary chosen nonzero apolar vector at a least degree `r₀`, a nonzero moment vector, the original bounds `1≤r₀≤D/2+1` and `r₀≤D`, and the vanishing of **every** lower apolar kernel. It does not require an initially nonzero top coefficient or uniqueness in a balanced kernel. The audited chart-selection lemma supplies `z` with transformed last coefficient `a≠0`. Pointwise scaling by `a⁻¹` gives `b_(r₀)=1`, `b≠0`, and preserves apolarity through the audited complex-linear apolar map. The affine polynomial is the exact dehomogenization of `b`; the proof independently establishes its top coefficient is one, `natDegree=r₀` exactly, monicity, and each coordinate equality `q.coeff i=b_i`. It therefore satisfies the coefficient and degree interface required by the conditional normalized quotient proof.

The inverse-dual moment chart is an equivalence, so the transformed moment vector remains nonzero. The all-degree apolar-kernel transport theorem sends any hypothetical nonzero transformed vector of lower degree back to a nonzero original one, contradicting the supplied lower-kernel hypothesis. The proof covers `k=0` and every `k<r₀` with `k≤D`; it does not quietly check only the preceding degree. The balanced endpoint and `r₀=1` are included by the signatures. The zero moment vector belongs to a separate branch of the frozen target and is not assigned a positive least degree.

The separate imported audit exited zero in pinned Lean 4.33.1, checked the complete exported signature, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]` as the theorem's transitive axioms. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`. Changed source bytes require a new review.

The theorem does not yet derive original-coordinate Hankel middle rank, ordinary-to-symmetric width equivalence, or the all-width frozen `Target`. Those are independent remaining obligations.
