# SP-14 weighted Sobolev maps and sharp projection estimates: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen source as the concrete weighted-sequence geometry required by the previously audited abstract oversampling theorem. It does not establish the background-dependent inverse estimates or the SP-14 negative target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/WeightedSobolevOperators.lean` | `f0368eb90ab2af9bdbdce1405c1bae511e4c1868ff95015d575cde65fd07b0f1` |
| Mathematical and numerical precontract | `194d333896e57d5dc11f638dfcf0646f94fc95bfff9f1fbe0e69353058178df8` |
| Independent preimplementation review | `b504db5cfe1f2df2b3568d4abc6716e229d6f5213db18a8c9e6e056bcea9bc6c` |
| Audited physical-space module | `ea0166080ec91c5df4da14e2f38eca5fc2a7f9271866099aad1fb8f46e5ba109` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `NLA.Statements.SP14` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit `/private/tmp/sp14-weightedsobolevoperators-independent-audit.lean` | `185720a0a21c08ebd6cfb3a67481dae79335b50b576508270a5b409291ca556d` |

The three exported operators are actual continuous complex-linear maps between the complete weighted `ℓ²` carriers. The inclusion from `H^(s+τ)` to `H^s` multiplies weighted coordinates by `(n+1)^(-τ)` and preserves the **physical** coefficient at every `n`. The truncation is the literal projector onto indices `n<h`, so `P_h²=P_h`, `P₀=0`, and `‖P_h‖≤1`. The finite lift multiplies indices `n<h` by `(n+1)^τ`, vanishes elsewhere, preserves each retained physical coefficient, satisfies `L₀=0`, `‖L_h‖≤h^τ`, and `ιL_h=P_h`. No index `n=h` is retained.

The all-sequence tail estimate compares each retained tail coordinate at `n≥q` with `(q+1)^(-τ)` and applies the `ℓ²` norm comparison, yielding exactly `‖(I-P_q)ιx‖_s≤(q+1)^(-τ)‖x‖_(s+τ)`. It includes `q=0`. The finite-band proof first establishes `L_hP_h=L_h`, then uses its operator bound to obtain the stronger required `‖L_h y‖_(s+τ)≤h^τ‖P_h y‖_s`, including `h=0`. These are the source's sharp factors; the pre-review's exact rational example and single-mode endpoint checks remain valid. No finite sample substitutes for these universal norm proofs.

The imported independent LeanCert audit exited zero in pinned Lean 4.33.1. It checked all three CLM types, the physical-coordinate formulas, norm bounds, projection/lift identities, and both sharp estimates; it reran `#assert_trust kernel` for nine principal theorems and printed only `[propext, Classical.choice, Quot.sound]` for each. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The previous abstract right-inverse theorem can now use these precise spaces and projection estimates as inputs. It still requires compatible inverses and numerical bounds for the actual background operator `𝒜_g`; this module supplies no such estimates. The forcing, nonlinear correction, infinite symbol, nonextension, spectral gap, and frozen `Target` remain open.
