# SP-14 positive endpoint and ratio: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this narrow gate for aggregate import. The frozen source proves the positive Laurent endpoint factor and the continuous negative quotient extension. Its Wiener norm bound and the full SP-14 Target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/PositiveEndpointRatio.lean` | `fa7bf264bf07eae3d21e368e368f1df38b554656154bdaa1702a3baac86b397d` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-positive-endpoint-ratio-independent-audit.lean` | `5f03e4bb217b78120a066b852d334951644fb24bd6c4576788393b0714287c55` |

For every finite positive Laurent coefficient vector, the recursion `q₀=0`, `qⱼ₊₁=pⱼ−qⱼ` gives `P₊=(1+s)Q₊−qᵥsᵛ⁺¹`. Evaluating at `s=-1` and using the separate positive contact premise forces the terminal coefficient `qᵥ=0`. The resulting `Q₊` has the same finite length, including the zero-length case. This is the exact factorization required by the reviewed contract.

The negative quotient extension is the actual continuous function `s*g₀(s)*Q₋(s)`. It vanishes at `-1`. The source proves `g₀(s)≠0` away from `-1` using its audited boundary square identity, then derives `P₋(s)/g₀(s)=s*g₀(s)*Q₋(s)` from `P₋=(1+s)Q₋` and `s*g₀²=1+s`. The equality is claimed only where division is defined.

The direct pinned Lean 4.33.1 build passed 2,769 jobs. A separate imported audit checked all five public theorem signatures, reran LeanCert `#assert_trust kernel`, and reported only `[propext, Classical.choice, Quot.sound]`. The source has no proof escape. Changed source bytes require a new review. The literal W⁰ ratio estimate, full curve bound, two-mode numerical witness, and original negative Target remain open.
