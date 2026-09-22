# Independent module review: exact trimming concentration

Verdict: **APPROVE**, module-only. Reviewer: Codex AI agent `/root/infrastructure_audit`, 2026-09-22. Both reviewed modules were authored by `/root/reference_review`; this reviewer authored neither and authored none of their rebuilt project dependencies. The reviewer did author separate IE-21 spherical/Gaussian modules, so this is not a fresh independent final review of the complete package.

| Module | SHA-256 |
| --- | --- |
| `NLA/IE21/BoundedConcentration.lean` | `1b0eea5beaabaefd8dd6b15df3f5b4a71eb620f9ee13b67949c467c96675c7b3` |
| `NLA/IE21/TrimmingConcentration.lean` | `04828fc5953c3814a12abbe5056d90cddd2208d0bf1b94d6fc904f9543721c83` |

Both full sources were read against the frozen definitions and pointwise concentration target. All nine rebuilt project source hashes match the author receipt; all four frozen boundary hashes remain unchanged. These modules prove generic concentration helpers, with the spherical-law specialization still to be assembled separately.

The bounded Hoeffding upper tail applies Mathlib's interval result with sub-Gaussian parameter L²/4 to the centered variables, retaining independence under measurable composition. At deviation mLε, the sum parameter mL²/4 gives exactly exp(−2mε²). This matches the inspected upstream theorem signatures. The strict event is included in the non-strict tail event in the correct direction. Reflection in L gives the lower tail with mean L−a; its integral calculation has bounded integrability. The two-sided event is covered by these two tails, with factor two. The proof requires m≥1 and L>0, and includes ε=0 without dividing by ε.

`retainedRows_bounds` retains the actual natural floor of θm. It proves k≤m, k≤mθ, and |k−mθ|≤1 using the floor inequalities, including m=0 in this helper. `finiteTrim_fractional_mean_error` uses m≥1, exact cardinality k, the earlier fractional comparison, and two sample deviations. The one-unit floor discrepancy contributes L before division by m, producing precisely L/m; the other two contributions give 2Lε. No floor term is dropped or absorbed into an asymptotic constant.

The generic concentration theorem quantifies over arbitrary measurable probability spaces and measurable independent samples with the literal common law. Its variable Y is nonnegative, integrable and has mean one. The quantile selector handles atoms and ties by fractional threshold weight, with exact mean θ and actual populationTrim as the mean of YW. It proves YW∈[0,L], while W and the indicator C of Y≤L lie in [0,1]. All means are transported through the common-law map rather than assumed for the samples.

The count indicator includes equality at L. From L(1−C)≤Y and L=2/(1−θ), its mean q satisfies q≥θ+ε for the complete range 0<ε≤(1−θ)/2, including the upper endpoint. Outside its strict lower-tail event, the observed count is at least m(q−ε)≥mθ≥floor(θm). Thus the threshold hypothesis needed for exact finite trimming follows even on the event boundary. The selector and weighted-selector bad events each have two Hoeffding tails; the count event has one. The proved inclusion into their union yields exactly the source coefficient 2+2+1=5 and exponent −2mε². No independence between these three derived event families is asserted or needed.

The proof allows k=0, tied observations, atoms at the quantile, and equality on all good-event boundaries. It uses the same deterministic exact minimum as the frozen target; no relaxed selection or rank assumption appears. No defect was found.

Fresh check command: `python3 reviews/concentration-referee-infrastructure-evidence/build.py`. A new external directory was used. Lean 4.33.1 (compiler 819816b2e0a3bf405af45ae5c7af2491d8f5bee6) compiled all nine project sources and the audit, all exit 0 with no Lean warnings/errors. The six public declaration closures are exactly `propext`, `Classical.choice`, `Quot.sound`. No reviewed implementation imports Challenge or contains sorry, admit, user axioms, unsafe or native_decide. The receipt binds all commands, logs, source hashes and closures, and source bytes remained unchanged throughout the run.

These are local macOS checks using retained pinned dependency caches, not fresh upstream source builds. The inspected Mathlib source's hash is recorded, with its retained-cache provenance limitation. This review does not claim that IE-21 has passed Linux sandbox verification, LeanCert kernel assertions, full Lean4 Comparator or negative controls; it does not authorize canonical status promotion on its own.
