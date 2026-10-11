# SP-14 negative restoration invisibility: independent pre-proof review

**Reviewer:** `/root/ra06_sampling_review` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `NEGATIVE_RESTORATION_INVISIBILITY_PRE_REVIEW.md` for implementation, with the contract's explicit source-parameter specialization retained as a final source-review gate. This is finite packet algebra and earlier-section persistence only, not a proof of the SP-14 counterexample.

The source uses `K_m(s)=(-s)^(-m−1)((1−s⁻¹)/2)^m`. Its finite binomial expansion has coefficient `(-1)^(m+1+r)·choose(m,r)/2^m` at frequency `s^(-m−1−r)` for `0≤r≤m`; the contract's sign is exact. At `s=-1`, every expanded term contributes `choose(m,r)/2^m`, so `K_m(-1)=1` and `D(-1)=L(-1)−L(-1)K_m(-1)=0`. The algebraic identity also covers `m=0`: `K_0(s)=−s⁻¹` and `K_0(-1)=1`, although the source's weighted-regularity lemma assumes `m≥2` for its analytic estimates.

Under `z↦zK_m(z²)`, the modes are exactly `−2m−1−2r`; hence the **restoring `K_m` term alone** is invisible in every section `n≤2m+1`, whose row-minus-column frequencies lie in `[-2m,2m]`. The current-stage `L_{m,q,v}` has modes `1+2(d−m)` for `d<q`, which may lie inside that section and is intentionally used to change it. The contract correctly avoids claiming the full `D` is invisible at its own order.

For earlier sections `n≤2p+1`, `8p≤m` and `2q≤m` imply, for every `d<q`, `1+2(d−m)≤2q−2m−1≤−m−1<−2p`; the restoring modes are smaller still. Thus the full `zD(z²)` is invisible to those earlier sections. The empty `q=0` case gives `L=0` and `D=0`, including `p=m=q=0`. The source's stage choice `m` divisible by eight, `q=3m/8`, and `m≥8p` satisfies `2q=3m/4≤m`; the eventual Lean source or its immediate application must check this arithmetic rather than assume it. The theorem's `ha : Continuous a` is the correct premise for interval-integral additivity, as established during positive-packet review; the finite packet itself is continuous.

The full frozen `SP14.Target` additionally needs selected correction vectors, jet equations, exact multiplicity, norm budgets, final infinite symbol, both annular nonextensions, test separation, and an empirical gap. None is supplied here.

| Reviewed input | SHA-256 |
| --- | --- |
| **`NEGATIVE_RESTORATION_INVISIBILITY_PRE_REVIEW.md`** | **`f77a84e78a6dd733d9e7fe5bf258de7b100fba4c15e9e735263121abf36a565b`** |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| `PositivePacketInvisibility.lean` | `90df55a41491c60d442df3679d1808c2c77a66d8e66fe8dbffe940151c3c8d1f` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |

Changed source bytes reopen this pre-review. No negative-restoration Lean source was present at this review.
