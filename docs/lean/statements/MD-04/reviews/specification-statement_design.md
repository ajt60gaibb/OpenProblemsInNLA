# MD-04: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Phase: preimplementation specification. Date: 2026-09-28.
Verdict: **approve** for the exact bytes below; no mathematical changes requested.

## Reviewed source identity

- matrix-discrepancy-and-optimization/MD-04/README.md: a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e
- docs/lean/statements/MD-04/NUMERICAL_TARGETS.md: b1713525efa62b36a87fcad78a1718a0b8d5d3a30015b7bfa303d9bedc8d79d8
- docs/lean/statements/MD-04/ORIGINAL.md: a8be36a5217cb0b3031c8f87cfc25e5421ca78dd8c42ecc151219fa62eb8156e

## Fidelity checks

1. A single positive real C is quantified before positive m,n, sparsity t, and every 0-or-1 real matrix. Natural t with 1<=t<=m exactly captures the source integer range.

2. The column count is the sum of 0-or-1 entries and is bounded non-strictly by t. The same sign vector has n entries each in {-1,1} and simultaneously bounds every row by C times the nonnegative real square root of t.

3. The source excludes t=0 and permits t=1 and t=m; the specification retains these exact endpoints. Zero columns, arbitrary incidence patterns and offline access to every column are included.

4. No dimension-dependent constant, online information restriction, algorithmic obligation, or stronger numerical value from the resolution is substituted.

5. The complete canonical README and ORIGINAL.md agree byte for byte, preserving all source context and mathematical credit.

## Limits

Independent preimplementation specification fidelity review only. This does not review a Lean implementation, prove the target, revalidate the cited solution paper, or certify any kernel/Comparator execution. Later actual Lean-boundary review remains necessary.
