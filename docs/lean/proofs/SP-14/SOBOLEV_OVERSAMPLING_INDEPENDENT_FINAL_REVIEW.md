# SP-14 Sobolev oversampling algebra: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen abstract-operator theorem for aggregate import as a partial SP-14 result. It does not prove the concrete Sobolev instantiation or the negative `NLA.Statements.SP14.Target`.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/SobolevOversampling.lean` | `fd9b5a433847dc8392070752a97244bebeedde08d4d7f7a198e24d64f6f27d77` |
| Independent exact mathematical pre-review | `b910616c49b33cf2331f79b519c4fc997ad5b2b945c0609fe77584f9302ed654` |
| Canonical `counterexample.tex`, “Oversampling from two Sobolev bounds” | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Separate imported audit source, `/private/tmp/sp14-sobolevoversampling-independent-audit.lean` | `62f937c1364da1df5d090fb6a6ce9828ba91e036c98cac6f78a205f55ab2dddd` |

The source definitions expose the exact operators `E=P_h A_s (I-P_q) B_s P_h` and `R=P_q B_s P_h (I-E)⁻¹` in the bounded complex-linear operator algebra. The public theorem includes the original `τ>0`, `q≥h`, compatible isomorphisms and inverses on both spaces, projection idempotence and norm bound, finite-band lift, the two **explicit** weighted tail/band inequalities, and individual bounds `M_s,K_s,K_r`. Its conclusion proves all five required facts: `‖E‖≤ε` for `ε=M_sK_r(h/(q+1))^τ`, `IsUnit (I-E)`, `P_qR=R`, `P_hA_sP_qR=P_h`, and `‖R‖≤K_s/(1-ε)`. The exact `q+1` denominator and strict `ε<1` are retained.

The norm proof first derives `B_sP_h=ι B_rL_h` from compatibility and the lift. It bounds the composed tail map and lift using the displayed input estimates, then applies submultiplicativity and the real-power identity, including `h=0`. For the inverse it proves `‖E‖<1`, constructs the ring inverse of `I-E`, and derives its norm bound directly from `U=I+EU`, using `‖I‖≤1`. Idempotence gives the range identity. The algebraic identity `P_hA_sP_qB_sP_h=P_h-E=P_h(I-E)` yields the right inverse. Finally the two projection norms and `‖B_s‖≤K_s` yield the exact output norm bound. There is no postulated right inverse.

Some source premises (`τ>0`, `q≥h`, the reverse inverses and forward operator compatibility) are not used in the abstract algebra derivation; keeping them matches the source lemma and does not weaken the conclusion. The uniform proof includes the zero-dimensional/`h=0` endpoint; the numerical rational `2×2` sign/order check belongs to the prior mathematical review.

The separate imported audit completed with exit code zero using pinned Lean 4.33.1 and LeanCert `kernel` mode. It independently checked all three exported types, reran `#assert_trust kernel`, and printed exactly `[propext, Classical.choice, Quot.sound]` as the theorem's transitive axiom set. A frozen-source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape.

The theorem is intentionally abstract. The literal weighted coefficient-sequence `H^s,H^(s+τ)` model, its truncation/tail estimates, actual background-dependent compatible inverse bounds for `𝒜_g`, the nonlinear stage, infinite symbol, and final counterexample remain separate obligations. Changed source bytes require a new final audit.
