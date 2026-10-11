# SP-14 negative restoration and earlier-section persistence: independent Lean review

**Reviewer:** `/root` (AI agent), 10 October 2026. **Verdict:** APPROVE frozen `NegativeRestorationInvisibility.lean` for its exact finite packet algebra and Toeplitz cutoff theorems. This is a partial construction; it does not prove the frozen negative `SP14.Target`.

The definitions match the approved source contract: `negativeL m q v s = Σ_{d<q} v_d s^(d−m)`, `restoringK m s = Σ_{r=0}^m (-1)^(m+1+r) choose(m,r) 2^(−m) s^(−m−1−r)`, `restoredD=L−L(-1)K`, and the actual circle perturbation is `z D(z²)`. The compiled `restoringK_source_formula` proves the finite sum equals the source's `(-s)^(−m−1)((1−s⁻¹)/2)^m` for every circle `s`, including `m=0`. The separate endpoint proofs establish `K_m(-1)=1` and `D(-1)=0`; for `m=0`, `K_0(s)=−s⁻¹` and the same endpoint identity holds.

The proof rewrites each finite packet term as a genuine circle mode under the frozen real-interval Fourier integral. The restoring term `zK_m(z²)` has modes `−2m−1−2r`, all strictly below the diagonals of a section `n≤2m+1`, so **that term alone** is invisible at its matching order. The raw negative correction `zL(z²)` has modes `1+2(d−m)` for `d<q`; it can change the selected `T_(2m+1)` and is not claimed invisible there. Under `8p≤m` and `2q≤m`, both the raw and restoring modes lie below `−2p`, so the **full** `zD(z²)` preserves every earlier section `n≤2p+1`. The public source-stage corollary checks `2*(3m/8)≤m` in Lean and therefore instantiates the exact source choice `q=3m/8` whenever the source's `m` is divisible by eight; it also proves the floor-valued variant for arbitrary `m`. The empty `q=0` and `m=p=0` endpoints are retained.

All Toeplitz equalities use the frozen row-minus-column index and exact `FourierCoefficient`, with continuous background `a` so both interval integrands are integrable before additivity or subtraction is used. The source does not replace the integral by a formal coefficient extractor. This module supplies finite persistence only: selected correction vectors, jet equations, multiplicity, regularity budgets, final infinite symbol, two-sided nonextension, and the empirical gap remain open.

I read the complete frozen source and reran a **separate imported LeanCert audit** under pinned Lean 4.33.1. It checked all five public definitions, elaborated the six public theorem signatures, ran `#assert_trust kernel` on each, and printed each transitive axiom set. The audit exited 0; every theorem uses only `[propext, Classical.choice, Quot.sound]`. The source contains no `sorry`, `admit`, custom `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac`.

| Reviewed input | SHA-256 |
| --- | --- |
| **`lean-statements/NLA/Proofs/SP14/NegativeRestorationInvisibility.lean`** | **`318f9d1b2a0af4bf8355aa78afc7440b9c83449b6b2f5de8bd1bc361ac36e476`** |
| Approved `NEGATIVE_RESTORATION_INVISIBILITY_PRE_REVIEW.md` | `f77a84e78a6dd733d9e7fe5bf258de7b100fba4c15e9e735263121abf36a565b` |
| Independent mathematical pre-review | `997f2fb8ab1dca58afc38be27cfad9e492439a964b70e058795e6bde084b773b` |
| Frozen `lean-statements/NLA/Statements/SP14.lean` | `2f8e69c4335d8a7a33d38756fce60957ca770af1415a54da5a66b7fa92611c00` |
| Canonical `counterexample.tex` | `34b917113c3031dee7f2b2f803d03a2eec0fb515582a29fa6c059870439522cd` |
| Imported `/private/tmp/sp14-negative-independent-audit.lean` | `a952211193ad1116f8dfb6f4c3b8ba31b003d94686ad0fcc7843ce6e6d548187` |

Changed source or contract bytes reopen this review.
