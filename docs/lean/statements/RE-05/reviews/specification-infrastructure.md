# RE-05 independent pre-implementation specification review

Reviewer: OpenAI Codex AI agent `/root/infrastructure`, 2026-10-09. I did not author the RE-05 specification or canonical page. Phase: `specification`. Verdict: **APPROVE** for implementation of the exact Lean statement. This is a statement review, not a proof audit or external human peer review.

## Reviewed inputs

| Input | SHA-256 |
| --- | --- |
| `randomized-and-low-rank-approximation/RE-05/README.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/ORIGINAL.md` | `e8958ad5574576a781613326cdc4ba125b4ee1c2a7f41c64e6adddda3a06772b` |
| `docs/lean/statements/RE-05/NUMERICAL_TARGETS.md` | `df935cbeef31796a83b9db2bc9d6f10a6a300d2d57cd3d0525d83646865d42f7` |

The retained `ORIGINAL.md` is byte identical to the canonical README. The permanent ID and path agree with `problem_ids.json`.

## Exact model, error, and query comparison

The specification keeps one uniform randomized algorithm and one set of absolute parameters `C>0` and natural `a,b` before every admissible accuracy, positive dimension, linearly independent explicitly supplied real matrix family of size `1≤q≤n²`, and arbitrary real target. It requires the returned `q` real coefficients to define a matrix in the actual span, without assuming the target belongs to it or adding a conditioning/rank restriction. The benchmark is the exact minimum Frobenius norm error, and the success event is the pure multiplicative `(1+ε)` inequality at probability at least `99/100` for every fixed input. This also correctly forces exact reconstruction on successful runs when the optimum is zero.

The target matrix remains accessible only through adaptive `Av` or `Aᵀv` vector queries, each charged once. Explicit basis matrices and ε are freely available. The proposed concrete exact-real operational model rules out hidden inspection of `A`; it permits the source's unrestricted intervening exact-real computation and Gaussian/SVD primitives without adding bit-cost or finite-precision obligations. The query cap is the source's exact `C sqrt(q) ε^(−a) [1+log(2+q)+log(1/ε)]^b` with natural logs, uniform over all data and random executions. In particular it is a worst-case count rather than an expectation or success-conditional cost.

The specification records the stronger nonadaptive construction and fifteen-fold amplification only as optional companion information. Its mandatory `Target` remains the original existential, uniform, `0.99` statement; it does not replace it with constant success, additive error, a fixed matrix family, or a numerical heuristic. I found no missing quantifier, changed probability threshold, error metric, arithmetic model, or query-count term.
