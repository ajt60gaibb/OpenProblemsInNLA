# RA-12 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The domain is exactly every nonzero real symmetric PSD matrix of every positive dimension and every positive integer sample count. Spectral norm, trace, effective rank mu and the non-strict epsilon>=2/(m*mu) threshold are retained. Positivity of norm/trace and 1<=mu<=n are consequences, not narrower input assumptions.

The Gaussian estimator uses the concrete product law of all m*d independent standard normal coordinates and the complete quadratic form. Marginal Gaussian laws alone are excluded. Each matrix uses its own dimension, and the probability comparison requires no coupling.

The extremizer has floor(mu) entries 1/mu and one residual entry (mu-floor(mu))/mu, including the zero residual entry at integral mu. Its dimension floor(mu)+1 can exceed the original dimension; this is allowed by the canonical statement.

Both comparisons are required with the same middle extremizer. All three events are two-sided with weak tail endpoints. The last law has shape=rate=m*mu/2, density on positive reals as written, and mean 1. A scale convention or a direct first-to-last inequality would change/omit the target.

Threshold equality, m=1, n=1, rank deficiency, zero eigenvalues and an empty lower-tail event remain included. The concrete joint law and density specify sufficient mathematical semantics; their actual Lean measure implementations and any ENNReal-to-real conversion still need boundary review.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

## Reviewed input hashes

- `randomized-and-low-rank-approximation/RA-12/README.md`: `4771d76230e0a37ccf706b9d7fc0824d257856835d099465963cd200c0adb573`
- `docs/lean/statements/RA-12/NUMERICAL_TARGETS.md`: `9bd0297d87682e08bd785045651b31fcd9f7f0f73ba29c1a0c2c0dc7018667a6`
- `docs/lean/statements/RA-12/ORIGINAL.md`: `4771d76230e0a37ccf706b9d7fc0824d257856835d099465963cd200c0adb573`
- `docs/lean/statements/RA-12/source-lock.json`: `ff98031f6231deeb28edec802a4d31b9945307fd47f1d4c97f5eb94f9d385843`
