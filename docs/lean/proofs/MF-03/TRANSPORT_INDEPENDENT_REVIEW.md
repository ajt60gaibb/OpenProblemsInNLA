# MF-03 disk-certificate transport: independent partial-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `Transport.lean` as an exact **conditional** transfer of one normalized-pair closed-disk certificate to every reduced normalized pair of the same order. It establishes no reduced-pair existence and does not prove the full MF-03 Target.

The theorem `disk_bound_for_every_reduced_pair` takes arbitrary `m` and a supplied pair `P₀,Q₀` with `NormalizedPadeRepresentation m P₀ Q₀` **and** a supplied full closed-disk certificate for that pair: for every complex `z` with `‖z‖≤3`, `Q₀.eval z≠0` and `‖1−P₀.eval z/Q₀.eval z‖≤2`. The witness pair need not be coprime. It then takes an arbitrary `P,Q` satisfying `ReducedPadeRepresentation m P Q` and concludes those same two inequalities for every such `z`. The tested pair's reducedness is an explicit theorem premise; no existence of such a pair is asserted or smuggled into the conclusion.

The independently reviewed `normalized_cross_product_eq` gives the exact polynomial identity `P*Q₀=P₀*Q` from the two normalized Padé conditions. Hence `Q ∣ P*Q₀`. Since `P,Q` are coprime, Euclid's lemma (with symmetry to put `Q` first) gives `Q ∣ Q₀`. Writing `Q₀=Q*R` proves that a zero of `Q` on the disk would be a zero of `Q₀`, contradicting the supplied certificate. Evaluating the cross product and dividing by the two now-proved nonzero denominators gives `P(z)/Q(z)=P₀(z)/Q₀(z)`; the supplied weak constant-two bound transfers without changing radius or boundary inclusion. This argument handles removable factors in an unreduced witness denominator correctly. It uses no order-specific coefficient estimate or unproved pole assumption for the tested pair.

This lemma is a genuine bridge for the Target's universal **every reduced pair** clause. It still requires, for every order `m≥1`, an actual normalized witness with a disk certificate and a separate proof that at least one reduced normalized pair exists. Cross-product equality alone does not supply that existence, nor does this theorem prove the witness's Padé equations or disk inequality.

I ran `lake build NLA.Proofs.MF03.Transport`, direct `lake env lean NLA/Proofs/MF03/Transport.lean`, and a separate audit requiring `.thmInfo`, `#assert_trust kernel`, and `#print axioms` for the exported theorem. All exited zero with pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. Its transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `NLA/Proofs/MF03/Uniqueness.lean` | `c781644e76a6143535a45862263e6776ee1257ff6ac2d69eed328dd63f73daa5` |
| **`NLA/Proofs/MF03/Transport.lean`** | **`902e6c7caf52f462d2bc11fcdf713306f69d67d8da0a159b01713ae31fc6cb66`** |
| `STATEMENT_INDEPENDENT_REVIEW.md` | `dff7af4c1fc3b352ef9afbaf422bf644cb77118297b81c71b6793baf080ef2e5` |
| Manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/mf03-transport-independent-audit.lean` | `eb27e318f7d3d06f19e89ed1e6c715b41ccf53aff8a6b17cd07f218db3f40221` |

Any changed mathematical source bytes require renewed review of the affected claim.
