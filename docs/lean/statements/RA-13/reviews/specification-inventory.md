# RA-13 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The matrix domain includes every nonzero real symmetric matrix, with indefinite and zero-trace cases explicitly retained. Spectral norm lambda, Frobenius norm phi and rho=phi^2/lambda^2 are exact; no PSD or nonzero-trace premise enters.

The extremizer has floor(rho) diagonal entries lambda plus lambda*sqrt(rho-floor(rho)), with nonnegative square root and a retained zero final entry at integral rho. Its own dimension is used for its Gaussian estimator. The full product Gaussian law, not only marginal normality, defines every estimator.

The source threshold is preserved exactly: 2lambda/m + sqrt(2phi^2/m+(2lambda/m)^2), including equality. The specification correctly follows the canonical displayed formula rather than the historically inconsistent prose limit.

The left event is a two-sided absolute-error event; both middle and final events are one-sided upper tails, each multiplied by exactly 2. The second comparison remains separately present, and 2*probability is not capped at 1.

The final Gamma distribution uses shape m*rho/2 and rate m/(2lambda), giving mean phi^2/lambda. The centering and shape/rate order agree with the canonical source. The stated normalization converts the threshold to 1+sqrt((m/2)*rho+1) without restricting signed spectra.

The concrete distribution, norm, matrix and event specifications are adequate for implementation. Their Lean definitions and all coercions/partial-parameter conventions require subsequent independent boundary review. No density shape conjecture or finite numerical experiment replaces either comparison.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

## Reviewed input hashes

- `randomized-and-low-rank-approximation/RA-13/README.md`: `16a973ffc9040332e2a521a6a2d2938dcb95df736304185f88ea195a8c78a377`
- `docs/lean/statements/RA-13/NUMERICAL_TARGETS.md`: `9cb1d0597b603f7db4576a65120df68e4eafa2e07491905804764094dd01861d`
- `docs/lean/statements/RA-13/ORIGINAL.md`: `16a973ffc9040332e2a521a6a2d2938dcb95df736304185f88ea195a8c78a377`
- `docs/lean/statements/RA-13/source-lock.json`: `3c358c1a4012489ff81379faafaefb75599dbf74235b8343076936dd8b00f947`
