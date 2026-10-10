# SP-14 finite positive literal Wiener size: independent final review

**Reviewer:** `/root`, 10 October 2026. **Verdict:** APPROVE this frozen literal finite-size gate for aggregate import. The full first-background bound and SP-14 Target remain open.

| Frozen input | SHA-256 |
| --- | --- |
| `lean-statements/NLA/Proofs/SP14/FinitePositiveWienerSize.lean` | `ecf1dbaac2fc87c99dae1c5ccbfbc424e431e36a0d8148ff58e2e24964be2fdc` |
| Exact canonical first-smallness contract | `c763ef118c85bbf178fea605a0ef9693932d287ed6308207c53b883ce4f9a596` |
| Separate imported audit `/private/tmp/sp14-finite-positive-wiener-size-independent-audit.lean` | `fe16c43256bac0cff6d0625e74fce74aa21be9e9aa72acb154fb0e6803125ff1` |

The actual positive Laurent term is a finite sum of distinct circle modes `j+1`. The source derives each coefficient using the frozen normalized Fourier interval integral; injectivity of `j↦j+1` means a frequency receives exactly one term. Summing the literal `(1+|k|)^(9/8)` weighted coefficient norms over all integers therefore gives exactly `Σⱼ(1+|j+1|)^(9/8)|qⱼ|`, with no omitted zero mode or shifted weight. The equality includes `v=0`.

The source separately establishes bilateral weighted Fourier summability by applying the independently reviewed finite positive multiplier theorem to the constant-one function, whose only Fourier mode is zero. The direct pinned Lean 4.33.1 build passed 2,773 jobs. A separate imported audit checked both public signatures, reran LeanCert kernel trust, and printed only `[propext, Classical.choice, Quot.sound]`. The source scan found no proof escape. Changed source bytes require a new review.
