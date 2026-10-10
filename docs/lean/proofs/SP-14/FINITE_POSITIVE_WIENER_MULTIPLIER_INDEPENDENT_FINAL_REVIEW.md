# SP-14 finite positive Wiener multiplier: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen positive Laurent multiplier gate for aggregate import. It is a constant-one weighted product estimate, not the complete first-background or SP-14 Target proof.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FinitePositiveWienerMultiplier.lean` | `50afbc4e3e2369e38fb8400e6dc4bec0bc985c9a83a857264cc19acbcd6dfc84` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-finite-positive-wiener-multiplier-independent-audit.lean` | `8d8e74dda8c1773c87e8a46067622a2d828d66988b41ce4c1d4e5c186b5d7405` |

The size `finitePositiveWienerSize v q` is the exact finite coefficient sum `Σⱼ(1+|j+1|)^(9/8)|qⱼ|`, with the required positive frequencies `j+1`. For the frozen normalized interval-integral Fourier coefficient, the source derives the exact shift `k↦k−(j+1)` in `f·P₊`, including the finite-sum interchange justified by continuity. The weight inequality follows from integer absolute-value subadditivity and `(1+a+b)≤(1+a)(1+b)` for nonnegative `a,b`; thus the constant is one, not an unspecified multiplier constant.

The source proves bilateral weighted Fourier summability of the actual product and then uses the integer-shift equivalence in its double series to obtain `W^(9/8)(f·P₊)≤W^(9/8)(f)·finitePositiveWienerSize(v,q)`. It works for any finite `v`, including zero. Its continuous and summable hypotheses are explicit and match the reviewed product gate.

The direct pinned Lean 4.33.1 module build passed 2,772 jobs. A separate imported audit checked both theorem signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review. Finite positive norm identification, the full `h−s` bound, two-mode witness, and the frozen negative Target remain open.
