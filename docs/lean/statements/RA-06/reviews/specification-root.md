# RA-06 independent specification review

**Verdict: APPROVE** for Lean statement implementation. The specification
author is `/root/inventory_review`; I independently compared its exact
mathematical/numerical contract with the complete canonical page and the
revised counterexample source. This review is not a proof or Lean-boundary
approval.

## Reviewed inputs

Published base: `0e916df335209819b5bf9bb8ed8f65ea978c049d`.

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RA-06/README.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/ORIGINAL.md` | `5ee10eb6d467ef6ebbd56955cdc95b2a1ff0613231d7e5ed6814679491d78f98` |
| `docs/lean/statements/RA-06/NUMERICAL_TARGETS.md` | `7036e298c8f74c4693fb638daf1aa22778756a9c26c53fbc39a9341e85f3d5e8` |
| `references/haidary-resolutions-2026-09-30/ra06-counterexample-revised.tex` | `21c5187b695e4469d803ceced320bd0314ade4702ed4567160f8ff835122cec7` |

The source copy and canonical README are byte-identical. The specification
keeps **every fixed real** `p>2`, ordinary sensitivities over all nonzero
real directions, arbitrary full-column-rank matrices, and the exact
independent Bernoulli retention rule with `1/n` floor, unit cap, and
`q_i^(-1/p)` scaling. Its energy expression is algebraically the sampled
`ℓ_p` norm power. The success event quantifies all input vectors for the
same retained-row outcome and uses both weak `(1±ε)` inequalities.

The original positive claim selects `C_p,c_p>0` before all matrices and
tolerances, then permits one common `α>0` to meet both expected-size and
probability `≥1−δ` requirements. The resolved `Target` is its negation for
**every** `p>2`, matching Theorem 5.1. The polynomial logarithm has the
correct `2nd/(εδ)` argument and natural logarithm; no fixed `p`, `ε`,
or dimension is substituted for the universal target.

As a source check, the complete-graph witness uses `n=binom(v,2)`,
`d=v−1`, `s_v=1/[1+(v−2)2^(1−p)]`, and
`S+d≤(2^(p−2)+1)v` (source lines 144 and 309–321). The
common-`q` source bound `nq≥(6^(−p)/3)vε^(−p)` follows from existence
of one successful graph (lines 404–441), without a `1−δ` factor. The
explicit `ε=1/b`, `δ=1/4`, `v=⌈b^(p+2)⌉` sequence (lines 452–478)
is represented as a proof witness, not a narrowed target. No substantive
mismatch was found. The eventual Lean definitions and imported meanings
still require independent review.
