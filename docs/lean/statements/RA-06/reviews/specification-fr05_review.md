# RA-06 independent pre-implementation specification review

Reviewer: `/root/fr05_review`, independent of the specification author.
Verdict: **APPROVE** for Lean statement implementation. This checks the
mathematical and numerical statement, not the counterexample proof.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/ORIGINAL.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| Revised counterexample source, `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |

The complete `ORIGINAL.md` is byte-identical to the canonical README
(`cmp` exit status zero) at published base
`0e916df335209819b5bf9bb8ed8f65ea978c049d`. The permanent registry
path remains `randomized-and-low-rank-approximation/RA-06/README.md`.

## Statement comparison

Canonical README lines 10–42 and the revised manuscript's target assertion
in its introduction specify **each real** `p > 2`, every full-column-rank
real `n × d` matrix, ordinary row sensitivity as the supremum over all
nonzero real vectors, and the precise independent rule
`qᵢ = min(1, 1/n + sᵢ/α)` with `α > 0`. The specification lines 9–57
preserves the ordinary sensitivities, additive floor, cap, exact real
`p`-powers, independent Bernoulli product law, rescaling
`qᵢ^(-1/p)`, and the expected count `∑ᵢ qᵢ`. Replacing the sampled matrix
norm power by `∑_{retained i}|aᵢᵀx|^p/qᵢ` is an exact identity for
`qᵢ > 0`, including the saturated branch `qᵢ = 1`.

Canonical README lines 27–40 demands one `α` meeting both the
`C_p ε^(-2)(S+d) log^{c_p}(2nd/(εδ))` budget and probability at least
`1−δ` that **both** weak inequalities hold for **every** real test vector
simultaneously. The specification lines 59–88 keeps these quantifiers,
the common `α`, exact success threshold, and constants depending only on
the fixed exponent `p`. Its `p`-power formula does not impose integer `p`.
The revised manuscript states all logarithms are natural.

The canonical resolution and revised manuscript Theorem 5.1 negate that
positive assertion for **every** fixed real `p > 2`. The specification
lines 90–105 states precisely `∀ p > 2, ¬ OriginalPositiveClaim(p)` and
unpacks its quantifier order; it does not replace the target with the
weaker claim that one prescribed parameter choice fails.

## Numerical counterexample comparison

The specification's grounded complete-graph construction (lines 107–151)
matches the source: `v ≥ 3`, `n = binom(v,2)`, `d = v−1`, equal sensitivity
`s_v = 1/(1+(v−2)2^(1−p))`, and
`S+d ≤ (2^(p−2)+1)v` (source Lemma 2.1). Its large-dimension condition
`v−1 ≥ 6^(−p) ε^(−(p+1))` is source equation `large-v`; its common-rule
bound `nq ≥ (6^(−p)/3)v ε^(−p)` and corresponding `(S+d)` coefficient
are source Corollary 4.2. The absence of a `1−δ` factor is correct:
that bound follows from even one successful realization at a fixed `q`.
The contradiction sequence `ε=b^(−1)`, `δ=1/4`,
`v=ceil(b^(p+2))` matches Theorem 5.1. These numerical witnesses may be
separate companion statements; the full negative original claim remains
the principal target.

I found no discrepancy or pre-implementation blocker. The arbitrary
nonnegative-weight strengthening is distinct from the original prescribed
sampler and is not substituted for it.
