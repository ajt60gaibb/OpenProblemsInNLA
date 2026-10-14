# MF-03 order-one certificate: independent proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 9 October 2026. **Verdict:** APPROVE the frozen `OrderOne.lean` as a Lean proof of **exactly the `m=1` clause** of the frozen MF-03 Target. It does not prove the all-order `Target`.

The module defines private complex polynomials `P₁=1+(5/12)z` and `Q₁=1−(1/12)z`. These match the manuscript and the first exact rational certificate record (`p=[1,5/12]`, `q=[1,−1/12]`). Their degrees are at most one and `Q₁(0)=1`. The proof checks the normalized Padé coefficient equations for **all** `j≤2`: `j=0` gives constant coefficient one, `j=1` gives `1/2−1/12=5/12`, and `j=2` gives `1/24−(1/12)(1/2)=0=P₁.coeff 2`. Thus it uses the exact series coefficient `1/(2j)!` through `2m=2`, without substituting an approximation.

`P₁` and `Q₁` are coprime by the explicit polynomial Bézout identity `(1/6)P₁+(5/6)Q₁=1`; therefore `order_one_reduced` proves an actual `ReducedPadeRepresentation 1 P₁ Q₁`. The module also proves **uniqueness of every normalized** order-one pair, not only reduced pairs: normalization fixes `Q.coeff 0=1`, the degree bound kills both second coefficients, the `j=2` Padé equation forces `Q.coeff 1=−1/12`, and `j=1` then forces `P.coeff 1=5/12`. Polynomial extensionality gives `P=P₁` and `Q=Q₁`. This justifies transport from the explicit pair to every reduced normalized representative in the Target's universal clause.

The independently reviewed `Disk.lean` lemma is applied with radius exactly three. For this pair its denominator tail is `T=|−1/12|·3=1/4<1`, and its numerator difference budget is `N=|5/12−(−1/12)|·3=3/2=2(1−T)`. Equivalently, the finite certificate has `B₁=1+T=5/4` and `N₁=3/2`, with zero slack for the weak bound. `order_one_disk` therefore proves `Q₁.eval z≠0` and `‖1−P₁.eval z/Q₁.eval z‖≤2` for **every complex** `z` on the full closed disk `‖z‖≤3`. At `z=3`, the quotient is exactly three and the error is two, so retaining `≤2` is necessary. The theorem `order_one_target_clause` combines this exact reduced-pair existence with the universal disk conclusion for **all** reduced order-one pairs. Its type is the body of `NLA.Statements.MF03.Target` specialized to `m=1`; it is not a theorem of `Target`, which requires every `m≥1`.

I ran `lake build NLA.Proofs.MF03.OrderOne`, direct `lake env lean NLA/Proofs/MF03/OrderOne.lean`, and a separate independent audit. All exited zero with pinned Lean 4.33.1, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert `621a43d7cf21f87872392a01e874f2f1dbddc926`. The audit required `.thmInfo` and passed `#assert_trust kernel` for `order_one_reduced`, `order_one_disk`, `order_one_unique`, and `order_one_target_clause`; every transitive axiom print was exactly `[propext, Classical.choice, Quot.sound]`. A source scan found no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`. The finite JSON's first record agrees with the Lean pair and budgets, but this module does not import or certify the remaining records.

The unresolved full-Target work includes orders `2,…,15`, the analytic all-order denominator and error estimates for `m≥16`, reduced-pair existence and uniqueness/transport at those orders, and the final universal theorem. No Linux Comparator acceptance is claimed for this intermediate module.

## SHA-256 of reviewed inputs

| Input | SHA-256 |
| --- | --- |
| Canonical `MF-03/README.md` | `57a39aef2af14ff19c83100fdb037de571ebb525ca836c045ddba6d91ae40f5a` |
| Frozen `NLA/Statements/MF03.lean` | `35f494bd3efdc2d710aa14927c9ee4f6664355199c331f85308f850a533f9f24` |
| `NLA/Proofs/MF03/Disk.lean` | `c7ced478264defa6a8365df21c2cb3d861adc18c37d67c793c3336df14d7f53a` |
| **`NLA/Proofs/MF03/OrderOne.lean`** | **`924c8437e430808f183ff104ee01ba9a1771ccf892a4bb9c37e26ad7c902ca48`** |
| `STATEMENT_INDEPENDENT_REVIEW.md` | `dff7af4c1fc3b352ef9afbaf422bf644cb77118297b81c71b6793baf080ef2e5` |
| `DISK_INDEPENDENT_REVIEW.md` | `a678ba33031072e01af5eaea8b100ad21a0fecc0fd7a858612909995fc057309` |
| Manuscript `MF-03.tex` | `312e90a79405a6cf0b116d5e3cc402a242107104f56b5abf542a18ff36247b` |
| `wave_kernel_finite_certificate.json` | `6d000c2b0b37acac1fca07bac239534d68177213da56f9c34aa5a5105c9cbaa8` |
| `lean-statements/lean-toolchain` | `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` |
| `lean-statements/lakefile.toml` | `1e061d7d0521587189437bc8a07b43fcc684889e70ca2e4a03e537e42b7b3a40` |
| `lean-statements/lake-manifest.json` | `a19377882192a9dbfc01c4d4e73edd887a8de91f735edabaeff2dfa38a4b4ec8` |
| Independent `/private/tmp/mf03-order-one-independent-audit.lean` | `1c49addc2dd1c9d5985ad28d3c9c69808bfbc66f32618950659ac3df3743b899` |

Any change to these mathematical source bytes requires renewed review of the affected claim.
