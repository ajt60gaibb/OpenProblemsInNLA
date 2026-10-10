# SP-14 weighted Wiener addition: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen constant-one addition gate for aggregate import. It is one component of the finite-background estimate, not the full SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/WienerAdd.lean` | `0bea73e31645b8fc0e6896a67b6285f218258f67781f84540c10c96bae8f4189` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-wiener-add-independent-audit.lean` | `5d03b2f197c651de91e836a4e7393351a9789dcbc196f5b598ceb48ebf051044` |

For continuous `f,g`, the source uses the actual normalized interval integral to prove `FourierCoefficient(f+g,k)=FourierCoefficient(f,k)+FourierCoefficient(g,k)`. Continuity supplies both interval-integrability premises. The complex norm triangle inequality and nonnegative literal `(1+|k|)^(9/8)` weight give the pointwise coefficient bound. Summing over all integer frequencies proves weighted Fourier summability of `f+g` and `W^(9/8)(f+g)≤W^(9/8)(f)+W^(9/8)(g)` with constant one.

The direct pinned Lean 4.33.1 module build passed 2,774 jobs. A separate imported audit checked both public signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source has no proof escape. Changed source bytes require a new review. Product and shift bounds for the full `h−s` estimate remain open.
