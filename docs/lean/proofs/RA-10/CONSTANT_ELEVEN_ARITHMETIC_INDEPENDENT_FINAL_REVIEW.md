# RA-10 exact constant-eleven arithmetic: independent final review

**Source author:** `/root/ra10_spectral_bridge`. **Independent reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this conditional real-arithmetic partial gate for aggregate import.

The exact precontract `CONSTANT_ELEVEN_ARITHMETIC_PRE_REVIEW.md` is SHA-256 `1753e6adac3c596bd4d2ddb3ac675874c57a8f58bf810ea6399c6873c9a10433` and was independently approved before implementation. The frozen source `lean-statements/NLA/Proofs/RA10/ConstantElevenArithmetic.lean` is SHA-256 `6dce48a3598747b1095b348985dcc70d64bc75b58a1bbfe4e20d0ebea8200857`.

I checked both exact imported signatures: `(g≥0 ∧ r≤e ∧ e₀≤e+r ∧ F−τs≤5g e₀+gr) ⇒ F−τs≤11g e`, and `(g,ε≥0 ∧ F−τs≤11g e ∧ e≤ετ ∧ gτ≤τs) ⇒ F≤(1+11ε)τs`. The only numerical step is `5e₀+r≤5e+6r≤11e`; every inequality is multiplied by a nonnegative factor. The statements include zero cases and do not divide by any source quantity. They are explicitly conditional and introduce no final-target premise.

The direct pinned Lean 4.33.1 build passed. My separate imported exact-signature audit `/private/tmp/ra10-constant-eleven-arithmetic-independent-audit.lean` is SHA-256 `4d6c2b98debc077aa02affc5b6ea1347b1f57e68e18161c00ea6ddd5a0085df0`; both LeanCert `#assert_trust kernel` checks passed, and both axiom reports were exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no proof escape. Changed source bytes require a new review.

This gate does not prove source matrix inequalities (15)–(18), identification with the frozen nuclear norms and truncations, the positive-integral representation, `TransferBound 11`, or frozen RA-10 `Target`.
