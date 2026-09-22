# IE-21 bounded source-fidelity audit

Date: 2026-09-22. Reviewer: `reference_review`, independent Codex AI agent. Scope: the complete canonical IE-21 statement and the complete retained IE-21/IE-22 manuscript, with detailed mathematical checks of Theorem 1 and Sections 2–5. Sections 6–7 were read for context; this report does not newly approve IE-22. No IE-21 definitions or proofs were authored or edited by this reviewer.

**Finding:** no blocking mathematical flaw or weakening of the canonical IE-21 target was found in the manuscript's proof route. The constants and the arbitrary-aspect-ratio conclusion check out as detailed below. This is a bounded source audit, **not approval of the mutable Lean statement draft, not a formal proof, and not a status-promotion receipt**. The forthcoming frozen Definitions/Challenge/NUMERICAL_TARGETS require separate independent review.

## Complete target and conventions

For fixed `0<θ<1`, retain exactly `k=floor(θm)` rows and minimize their Euclidean image norm over the full unit sphere. The minimum is attained: the sphere is compact and nonempty in positive dimension, each row-set objective is continuous, and the finite row-set family is nonempty. Swapping these two actual minima is legitimate. The variational least singular value is zero for a retained map with nontrivial kernel; using the smallest *positive* singular value would be wrong. The empty retained set has value zero. Squaring commutes with these nonnegative attained minima.

The matrix norm is the Euclidean induced operator norm, not the entrywise maximum, Frobenius norm, or an accidental default `Matrix` norm. For unit rows and `m≥1`, it is positive even when the matrix is rank deficient. A finite quantitative theorem may use `m≥1,n≥2`; the final sequence theorem must retain every sequence with `n→∞` and `m/n→∞`, discarding at most finitely many small-dimensional indices. No condition `k≥n`, `m/(n log n)→∞`, or independence across different sequence indices is needed.

The canonical constant must remain the displayed Gaussian integral. For standard real Gaussian `G`, continuity and positivity of its density give the unique `aθ>0` with `P(|G|≤aθ)=θ`; then

`hθ = E[G² 1{|G|≤aθ}] = θ − 2aθ φ(aθ)`, with `0<hθ<θ<1`.

The integration-by-parts identity is consistent, but need not replace the integral definition. Theta is fixed: the proof does not claim uniform estimates as theta tends to either endpoint.

## Trimming, distributions and concentration

1. **Finite optimizer and ties.** For nonnegative observations and `0≤k≤m`, the threshold maximum of `k t/m − (1/m)Σ(t−yᵢ)₊`, over `t≥0`, equals the average of the `k` smallest observations. Ties cause no problem. At `k=0`, choose `t=0`; no fictitious zeroth order statistic is needed. For the canonical range, `k<m` when `m≥1`.

2. **Population optimizer.** The selector-infimum definition has a nonempty feasible family (`w=θ`), nonnegative objective, and finite upper bound for integrable nonnegative variables. The continuous-law quantile selector attains it. The source's coupling inequality `|Hθ(Y)−Hθ(Z)|≤E|Y−Z|` is valid, but the joint-selector-to-marginal step requires a conditional-expectation/law-invariance proof. A simpler implementation route is to prove the genuine threshold dual `Hθ(Y)=sup_{t≥0}(θt−E(t−Y)₊)` and use the pointwise 1-Lipschitz property of the positive part. Neither route permits an unproved infimum/quantile correspondence.

3. **Sphere and Gaussian semantics.** For normalized surface measure on `Sⁿ⁻¹`, `Yₙ=n u₁²` has mean one and a continuous law when `n≥2`. The continuity assertion intentionally excludes `n=1`. The Gaussian polar decomposition must prove that a direction with this actual surface law is independent of the radius and that `Ru` is the standard Gaussian vector. Defining “uniform” to mean Gaussian direction without proving equality to normalized surface measure would leave a target-correspondence gap. Arbitrary independent rows with these laws must be transported to the chosen product law.

4. **Pointwise constants.** With `L=2/(1−θ)`, the theta-quantile `b` satisfies `b(1−θ)≤1`, hence `b≤L`. The count and truncated-sum Hoeffding events cost `4 exp(−2mε²)`. Markov gives `P(Yₙ≤L)≥(1+θ)/2`; the additional shortage event costs `exp(−m(1−θ)²/2)≤exp(−2mε²)` for `0<ε≤(1−θ)/2`. On their common complement, the discrepancy between the threshold count and `k` is at most `mε+1`. Removed observations are at most `b≤L`; if observations must be added, the shortage event's complement bounds them by `L`. Thus the exact error is `2Lε+L/m` and the failure coefficient is **5**. For `k=0`, the lower trimmed mean satisfies `hθ,n≤θ<1/m`, so the claimed bound still holds. It is not necessary to assume a nonempty retained set.

5. **Spherical moments and covariance constants.** The exact moment is

   `E Yₙʳ = nʳ (2r−1)!! / [n(n+2)…(n+2r−2)] ≤ 2ʳ r!`.

   The `r=0` convention is one; positive orders suffice for concentration. For `r≥1`, `E|Yₙ−1|ʳ≤4ʳr!`. The centered linear term vanishes, and for `|λ|≤1/8` the remaining exponential series is at most `16λ²/(1−4|λ|)≤32λ²`. Hence the MGF is at most `exp(32λ²)`. Taking `λ=u/64` gives the two-sided bound `2 exp(−mu²/128)` for `0<u≤1`. At net threshold `u=t/2`, a 1/4-net of size at most `9ⁿ` and the factor-two symmetric quadratic-form estimate give exactly `2·9ⁿ exp(−mt²/512)`. Neither independence among net directions nor stronger sub-Gaussian estimates are used.

6. **Uniform directions.** On `‖C−I‖≤t`, where `C=(n/m)AᵀA`, each retained covariance is positive semidefinite and bounded above by `C`, hence has norm at most `1+t`. Its quadratic form is `2(1+t)`-Lipschitz on the unit sphere. The minimum over all row subsets has the same Lipschitz bound. A delta-net of size at most `(1+2/δ)ⁿ` therefore gives

   `D = 2Lε + L/m + 2(1+t)δ`.

   The sharp volume-comparison cardinality must be proved; compactness alone only yields an unspecified finite net.

7. **Gaussian comparison.** With the independent radius, `G₁²=(R²/n)Yₙ`. Since `EYₙ=1`, independence gives `E|Yₙ−G₁²|=E|1−R²/n|≤√(2/n)` using `E R²=n`, `Var(R²)=2n` and Cauchy–Schwarz. This yields `|hθ,n−hθ|≤√(2/n)`. The source uses the full radius law, not merely equality of one-dimensional marginals.

## Exact quantitative theorem and limiting parameters

For `m≥1,n≥2`, `0<t<1`, `0<δ<1`, `0<ε≤(1−θ)/2`, outside an event of probability at most

`F = 2·9ⁿ exp(−mt²/512) + 5(1+2/δ)ⁿ exp(−2mε²)`,

the proof simultaneously gives

- `|(n/m)sθ(A)²−hθ| ≤ D+√(2/n)`;
- `|(n/m)‖A‖₂²−1| ≤ t`;
- `|sθ(A)²/‖A‖₂²−hθ| ≤ (D+√(2/n)+t)/(1−t)`.

For the last line, write the ratio as `a/b`. The covariance event gives `b≥1−t>0`, and `|a−hθb|≤|a−hθ|+hθ|1−b|`, with `hθ≤1`. The coefficient of `t` and denominator `1−t` are therefore correct. A failure upper bound exceeding one for small dimensions is harmless; it becomes useful along every canonical sequence. Measurability of the finite-minimum/compact-minimum and norm error events still needs explicit Lean proofs.

Let `Q=m/n` and eventually set `t=ε=δ=32√(log Q/Q)`. As `Q→∞`, these become positive, tend to zero, and satisfy every theta-dependent range restriction. The covariance exponent is exactly `n log 9−2n log Q`. For sufficiently large `Q`, `log(1+2/δ)≤log Q`; thus the other exponent is at most `−2047n log Q`. Both failure terms vanish. Since `n→∞`, also `√(2/n)→0`, and since `m→∞`, `L/m→0`. Eventually `1−t≥1/2`. This proves all three probability limits and the source's error order

`Oθ(√((n/m)log(m/n)) + n^(−1/2) + m^(−1))`

on an event with the explicit probability bound. It is neither an almost-sure assertion nor a claim of optimal rate. There is no hidden growth comparison between `Q` and `log n`.

## Implementation dependencies and review limits

The pinned Mathlib files inspected provide real foundations: `Measure.toSphere`, its finite/nonzero mass results, and `measurePreserving_homeomorphUnitSphereProd`; `stdGaussian`, orthogonal transport and projection variance; and bounded-variable `HasSubgaussianMGF`/independent-sum inequalities. Their availability does not establish the needed combined bridges. The main new developments are normalized surface probability and Gaussian polar laws, exact moments, scalar trimmed-mean semantics, dimension-explicit net bounds, quadratic-form concentration, and measurable transport to arbitrary independent row families.

No numerical interval certificate is needed for the displayed constants. Exact algebra and analytic inequalities suffice; any LeanCert use must still be in kernel mode. The original proof attribution remains Matthew J. Colbrook. Historical source text about provisional IDs and unavailable sources is superseded by the retained mapping review; it does not authorize changing IE-21's ID or original statement. This audit adds no authorship or completion claim to the formalization package.

## Hash-bound inputs

All hashes below are SHA256 of actual bytes, not hashes copied from source comments. The exported manuscript's current complete hash differs from the archived submitted proof because of added front matter. Independently extracted Sections 1–7 are byte-identical in both files, with SHA256 `71d588f052e02abf3ae00037be8ff6a08a3c8d1137faa653583a38ec0678124d`. The archived complete hash matches the historical review's `4b55…` receipt. No fresh external literature search was needed for this source-fidelity task; no publication-priority claim is made.

```text
1d5b73606664dd9af13078553f3311cabd947543b83a093f4060c5765cf42a6a  linear-systems-and-elimination/IE-21/README.md
0bbbf570e1a82736d8a4726e3733df0179735678e46c634dfc57d85ce4334c8b  linear-systems-and-elimination/IE-21/problem.tex
31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880  references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex
4b55fc68e12eb60e8e877622076b6b593d7a15566d6316d3cabf5df488437d39  references/colbrook-recovered-2026-09-11/submitted/proofs/IE-21-22.tex
d174419a6f71de369b7608a53b36dffa9cd815e3fd65a70d16457318cb68234d  references/colbrook-recovered-2026-09-11/verification/reviews/IE-21-22-review.md
86b191b9dfa5ddb104aab15b163aa7538245a9abf2323a60acad639e1151a2d7  references/colbrook-recovered-2026-09-11/README.md
8b79a8f73f2b91ad3270a516b34d00786b3c2aedf6af6aa48fb340cefcd7cc5b  docs/lean/campaign/2026-09-22/IE-21-NEXT.md
b607c37f99fe1cb718e1ad874ad2ef214d95f9aa8b5c2ad25033ca3a7965ff43  docs/lean/campaign/2026-09-22/next-target-linear-assessment.md
```

Pinned Mathlib revision: `0df444a360eaa60ab8c11dca51a86af692955474` (Lean 4.33.1); local source inspected under `/private/tmp/mf21-mathlib-source-20260920/Mathlib`.

```text
fc6efc9291ce6bcc2d8310b16f60087621470d2eb9cc10a0bfe47ebf413fabda  Mathlib/MeasureTheory/Constructions/HaarToSphere.lean
1fec35cf781da1009c37db80a96b05d70f2296ca7768e19bfc0b6314c9b43d49  Mathlib/Probability/Distributions/Gaussian/Multivariate.lean
7259bc145c6de9bb81b8aea24a660b951f12787ffdb7514ba27de74fb658e151  Mathlib/Probability/Moments/SubGaussian.lean
```
