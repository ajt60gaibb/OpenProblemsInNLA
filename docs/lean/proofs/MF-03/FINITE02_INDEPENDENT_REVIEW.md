# MF-03 order-two rational certificate: independent partial-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE frozen `Finite02.lean` as an exact normalized `[2/2]` Padé certificate with the full closed-complex-disk bound for its one supplied pair. It does **not** prove that this pair is reduced, that a reduced order-two pair exists, the universal reduced-pair clause, or the all-order MF-03 Target.

The private complex polynomials are represented by `Polynomial.ofFn 3` with exact coefficient lists

```text
P₂ = 1 + (115/252) z + (313/15120) z²,
Q₂ = 1 − (11/252) z + (13/15120) z².
```

These agree byte for byte in rational values with the order-two record of `wave_kernel_finite_certificate.json`. `ofFn 3` and the proof establish both natural degrees at most two and `Q₂(0)=1`. `order_two_normalized` checks the exact convolution with `1/(2j)!` for **all five indices** `j=0,1,2,3,4`, exactly the frozen `NormalizedPadeRepresentation 2` condition. Independently recomputing those five rational equalities gave `1`, `115/252`, `313/15120`, `0`, `0` on both sides. No sampled or truncated complex-disk test replaces these equations.

For the already-reviewed disk lemma, the exact denominator total and numerator-difference budgets at radius three are

```text
B₂ = Σ_{j=0}² |q_j|3^j = 1913/1680,
T₂ = B₂−1 = 233/1680 < 1,
N₂ = Σ_{j=0}² |p_j−q_j|3^j = 47/28,
2(1−T₂)−N₂ = 37/840 > 0.
```

Thus `order_two_disk` proves `Q₂.eval z≠0` and `‖1−P₂.eval z/Q₂.eval z‖≤2` for **every complex** `z` with `‖z‖≤3`, boundary included. The source certificate records the sharper ratio `N₂/(2−B₂)=2820/1447<2`; the Lean theorem intentionally exports only the weak bound required by the canonical target. Its proof checks the budgets by exact rational `norm_num` and calls the general coefficient-budget disk lemma, avoiding exhaustive complex-disk computation.

The module contains no `IsCoprime P₂ Q₂` theorem. The fact that one normalized pair exists and has a disk certificate is not the Target's explicit existence of a **reduced** normalized pair. The separately reviewed `Transport.lean` can transfer this disk estimate to any reduced normalized order-two pair **if one is supplied**, but it does not construct one. Orders other than two and the all-order analytic argument also remain open.

I ran `lake build NLA.Proofs.MF03.Finite02`, direct `lake env lean NLA/Proofs/MF03/Finite02.lean`, and a separate audit requiring `.thmInfo`, `#assert_trust kernel`, and axiom printing for both public theorems. All exited zero with pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`; each theorem's transitive axioms are exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `NLA/Proofs/MF03/Disk.lean` | `c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a` |
| **`NLA/Proofs/MF03/Finite02.lean`** | **`d1127741afc7ec96469d2a9d6e6c4f6be08d3e1e49cf7bb807760ffc2119097e`** |
| `wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `STATEMENT_INDEPENDENT_REVIEW.md` | `dff7af4c1fc3b352ef9afbaf422bf644cb77118297b81c71b6793baf080ef2e5` |
| `DISK_INDEPENDENT_REVIEW.md` | `a678ba33031072e01af5eaea8b100ad21a0fecc0fd7a858612909995fc057309` |
| Manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/mf03-finite02-independent-audit.lean` | `2f49945c9092d3401e13ea7663a0535871a7367ac11650649344bfb3ffb0c1a6` |

Any changed mathematical source bytes require renewed review of the affected claim.
