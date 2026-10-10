# TR-14 moment index: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `MomentIndex.lean` for the exact zero/nonzero foundation of the frozen TR-14 Hankel tensor. This partial result does not prove the arbitrary-width target.

I read the complete source after the mathematical [moment-algebra pre-review](MOMENT_ALGEBRA_INDEPENDENT_PRE_REVIEW.md) and checked its two public theorem signatures against the frozen `HankelIndex` and `Hankel`. The bounded-digit induction constructs, for every `0 ≤ j ≤ m(n−1)`, exactly `m` digits in `Fin n` whose sum is `j`. The zero-digit and `n=1` recursion endpoints are handled by the private lemma; the public surjectivity theorem retains the source range `m≥3`, `n≥2`. It uses equality of `Fin` indices, not an unbounded natural-index shortcut.

Surjectivity then evaluates the frozen tensor equality `Hankel h=0` at a multi-index for each moment coordinate. This proves `Hankel h=0 ↔ h=0` for **every** target-range `m,n,h`, including the zero moment vector and the extreme coordinates `0` and `m(n−1)`. The reverse direction is definitional. No genericity, nonzero-moment, rank, or chosen-width premise is introduced. The finite apolar quotient, catalecticant rank, and ordinary-to-symmetric implication remain open.

I independently ran an imported LeanCert audit under pinned Lean 4.33.1, separately from the author's build. It elaborated both exact public signatures, ran `#assert_trust kernel` for each, and printed transitive axioms. The audit exited 0; each theorem depends only on `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/TR14/MomentIndex.lean`** | **`93932adde8ff14713d19a1c813a0ec2ea09a319cff29af242b5028a51ac39435`** |
| Approved `MOMENT_ALGEBRA_PRE_REVIEW.md` | `2297de29286de55999709753278dcf84c1b4dd67640f4064baa98ba93165a840` |
| Independent mathematical pre-review | `133ebbb523bc26f7b806c5dc9d4ba93cd0d8becc2ce4acb015278f6a8af74761` |
| Frozen `lean-statements/NLA/Statements/TR14.lean` | `515387732a4aff4c343625d7578d687fa9d11255ddeaaeb278b9410e55e02dc9` |
| Canonical `README.md` | `a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86` |
| Canonical `solution.tex` | `0089d218f9f578e2ab21542c238a4025a4d98d7a32f66b25656c282716c14bc6` |
| Imported `/private/tmp/tr14-momentindex-independent-audit.lean` | `2f4d01ccaa06ab1e3383b72f4f6356b7bf3c00a70408e6248903aa41d9ba31c4` |

Changed source or contract bytes reopen this review.
