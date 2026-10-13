# SP-14 literal first Wiener sizes: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE the frozen first canonical-size gate for aggregate import. It proves exact finite Laurent W⁰/W⁴ sizes and the exterior base factor's W⁰ bound; it does not prove the remaining smallness conditions or full SP-14 Target.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/CanonicalFirstWienerSizes.lean` | `b640412b39b505a795f70ab59cdd0f18bb3b006c5f8afdc29e4db1dc53ab78f8` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Independent mathematical pre-review `CANONICAL_FIRST_SMALLNESS_INDEPENDENT_PRE_REVIEW.md` | `b6bfcb6a0a5f1d73a617abf54bbfe65539f617f30257aab38f3b946363354a92` |
| Separate imported audit `/private/tmp/sp14-canonical-first-wiener-sizes-independent-audit.lean` | `b6534cca0be136ce96b4811335df654e26e2dd74892f8975881fd5fbc023b2ad` |

The source defines `wienerSizeAt β` from the frozen all-integer interval-integral Fourier coefficient and literal `(1+|k|)^β` weight; at `β=9/8` it is definitionally the previously audited weighted size. Finite Fourier linearity and pure-mode orthogonality yield an exact singleton coefficient at each distinct Laurent frequency. Summing over all integers gives `W⁰(P₋)=Σ|p_j|` and `W⁴(P₊)=Σ(j+2)^4|p_j|`, including zero-length lists. The positive modes are `j+1`, so there is no missing weight shift.

For the actual exterior base factor, the source justifies termwise integration using the previously proved absolute half-binomial coefficient sum and a uniform norm-one phase bound. It proves `ĝ₀(k)=baseCoeff |k|` for every `k≤0` and zero for `k>0`. Bilateral summability follows from the coefficient summability, with the zero frequency counted once. The exact recurrence telescopes the nonzero coefficient norms and bounds every partial sum by two, giving the literal `W⁰(g₀)≤2`. No artificial coefficient norm replaces the Fourier integral.

The pinned Lean 4.33.1 direct module build passed 2,767 jobs. My separate imported LeanCert audit exited zero, checked the exact public definitions and all six public theorem signatures, reran `#assert_trust kernel`, and printed only `[propext, Classical.choice, Quot.sound]`. The frozen source scan found no `sorry`, `admit`, introduced `axiom`, `opaque`, `unsafe`, `native_decide`, `sorryAx`, `implemented_by`, or `run_tac` escape. Changed source bytes require a new review.

The endpoint positive quotient, continuous negative ratio, full curve smallness bound, nonzero two-mode witness, actual operator inverse, and complete SP-14 Target remain open.
