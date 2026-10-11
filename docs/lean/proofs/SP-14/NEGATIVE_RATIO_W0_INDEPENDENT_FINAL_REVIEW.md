# SP-14 negative ratio W⁰ bound: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen literal Wiener bound for aggregate import. It proves one numerical ingredient of the first finite background, not the full SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/NegativeRatioW0.lean` | `ea893c5b5332e1a2d03e1e7c93e1a0bd21b17ff7e3570e2aeb33376ba4e377f9` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-negative-ratio-w0-independent-audit.lean` | `35c4ded40b822acdc9e7e66e4d5a023ae793ff417983b1e5047fbe2a8c4b3ebf` |

The previously reviewed continuous quotient extension is exactly `g₀(s) Σⱼ qⱼ s⁻ʲ`. Its frozen interval-integral Fourier coefficient at integer `k` is therefore `Σⱼ qⱼ ĝ₀(k+j)`. The source proves this finite sum identity from termwise integration and the integer-mode shift. It then takes the complex norm, uses the finite triangle inequality, sums over every integer, and changes variables by the actual additive equivalence `k↦k+j`. The result is both bilateral Fourier norm summability and the constant-one bound `W⁰(negativeRatioExtension) ≤ W⁰(g₀) Σⱼ|qⱼ|`. The zero-length correction gives a zero sum with the same proof.

The direct pinned Lean 4.33.1 module build passed 2,770 jobs. A separate imported audit checked both public theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. The complete `h−s` bound, two-mode numerical witness, and full negative Target remain open.
