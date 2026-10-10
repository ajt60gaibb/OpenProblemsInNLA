# SP-14 circle-mode Wiener shift: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen literal W^(9/8) one-mode shift gate for aggregate import.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/WienerShift.lean` | `04137088894dfb865834ac17b8f26f1d298decff26038aa373633114d33a7d13` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-wiener-shift-independent-audit.lean` | `24b0baf9dc66d5a87949e4ae7540a9b690e89970b6ba8d6853899cc03364f39a` |

The source identifies the exact positive Laurent one-mode function with `s`, and its finite literal Wiener coefficient size with `2^(9/8)` because its only frequency is `+1`. The previously reviewed constant-one positive multiplier theorem then proves weighted Fourier summability of the actual product `s·f` and `W^(9/8)(s·f)≤2^(9/8)W^(9/8)(f)` for every continuous weighted-summable `f`. The factor has no spare constant or shifted frequency.

The direct pinned Lean 4.33.1 module build passed; a separate imported audit checked both theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. The full curve smallness estimate remains open.
