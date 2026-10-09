# RE-05 exact mathematical and numerical target

## Source and scope

`ORIGINAL.md` preserves the complete canonical `randomized-and-low-rank-approximation/RE-05/README.md` byte for byte. This document specifies the proposition before Lean implementation; it does not certify the Colbrook manuscript or supply a proof.

## Data, error, and quantifiers

One **uniform** randomized algorithm must work for every positive `n`, every `q` with `1 ≤ q ≤ n²`, every linearly independent explicitly supplied family `P₁,…,P_q` of real `n×n` matrices, every fixed arbitrary real `n×n` target `A`, and every real accuracy `0<ε<1/2`. The family spans the actual real subspace `𝓛={∑ⱼcⱼPⱼ:cⱼ∈ℝ}`. Independence is a hypothesis, not a promise that `A∈𝓛`. The algorithm returns all `q` real coefficients, hence a matrix in `𝓛`.

The benchmark is the attained minimum `OPT(A,𝓛)=min_{D∈𝓛} ‖A−D‖_F`, with the exact Frobenius norm, not the squared error unless equivalence is established. For each fixed admissible input, the returned coefficients obey `‖A−∑ⱼcⱼPⱼ‖_F ≤ (1+ε) OPT(A,𝓛)` with probability **at least 99/100** over the algorithm's internal randomness. If `OPT=0`, successful output must reconstruct `A` exactly. No additive error or rank/conditioning assumption is allowed.

## Oracle and exact-real computation

The only access to `A` is by matrix–vector queries `Av` or `Aᵀv` for chosen real vectors `v`; both directions cost one query. The explicit `Pⱼ` and ε are freely available. Queries may adapt to prior answers. Represent the algorithm by a concrete finite exact-real query program or an operational machine whose input cannot directly inspect `A`; the oracle response is the only route from `A` to its state. Do not use an arbitrary function of `A`, or an uninterpreted `Algorithm`/`Cost` relation that could silently perform extra queries. Every random execution should terminate with defined coefficients, including rank-deficient sketches. The event probability is over random draws for a fixed input.

Exact real arithmetic, comparisons, standard Gaussian sampling, and exact SVDs are permitted primitives. An `a×b` SVD conventionally costs `O(ab min(a,b))` arithmetic operations, but this target charges **only** calls to `Av` and `Aᵀv`. No bit complexity, finite precision, total arithmetic time, or nonadaptivity claim is part of the original.

## Query bound and numerical thresholds

There must exist one absolute real `C>0`, natural exponents `a,b≥0`, and the one uniform algorithm such that **every** execution uses at most

`C · sqrt(q) · ε^(−a) · [1+log(2+q)+log(1/ε)]^b`

oracle calls, with natural logarithms and exact real comparison to the integer count. The same `C,a,b` precede all data and random draws. This is a worst-case query cap, not a mean cap or a successful-run cap. The original permits adaptive queries and unrestricted intervening exact-real computation.

The affirmative resolution describes a stronger nonadaptive construction with `O(sqrt(q(log q+1/ε))+log q)` queries at constant success, followed by fifteen independent repetitions at internal squared parameter `ε/9` and a median selector. The retained source states failure at most `e^(−4.8)<0.01` and final norm factor at most `1+ε`. A named stronger companion may record these explicit figures if the source witness can be faithfully encoded, but `Target` must at least assert the complete original existential and `99/100` threshold above. Do not substitute constant-success or an additive-error result.
