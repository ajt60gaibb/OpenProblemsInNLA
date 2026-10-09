# MD-04 specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root`.

Phase: `specification`. Verdict: **APPROVED**.

Reviewed the complete canonical README, the complete retained `ORIGINAL.md`, and `NUMERICAL_TARGETS.md` before Lean target implementation. Canonical and snapshot bytes match.

- Canonical source SHA-256: `a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e`
- Specification input SHA-256: `b1713525efa62b36a87fcad78a1718a0b8d5d3a30015b7bfa303d9bedc8d79d8`

The universal constant C is chosen before m, n, t and A. Positive natural m,n and natural 1 <= t <= m represent the stated integer domain exactly, including both endpoints.

Every entry of A is exactly 0 or 1; the column hypothesis is its ordinary full sum bounded by t. Thus signed cancellation cannot falsely satisfy a sparsity hypothesis.

All n columns receive a -1 or 1 sign, including zero columns. All row inequalities use the same signing and the precise real factor C*sqrt(t). Positive m makes the pointwise row formulation equivalent to the stated infinity norm.

All displayed inequalities have the original weak endpoints. The nonnegative square-root convention is explicit; no division by sqrt(t), rounding, asymptotic-only range or extra probability model enters the target.

The specification retains the unrestricted offline existential claim, without importing the stronger numerical constant or requiring an algorithm. The complete original README is preserved byte for byte.

Independent specification fidelity review only. No Lean implementation, proof, cited-paper verification, or kernel/Comparator run is certified by this review.
