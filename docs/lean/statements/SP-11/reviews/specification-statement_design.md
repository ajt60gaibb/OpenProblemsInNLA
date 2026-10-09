# SP-11: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Phase: preimplementation specification. Date: 2026-09-28.
Verdict: **approve** for the exact bytes below; no mathematical changes requested.

## Reviewed source identity

- eigenvalues-and-inverse-problems/SP-11/README.md: 8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865
- docs/lean/statements/SP-11/NUMERICAL_TARGETS.md: a0cd200e8bd4dca2a9b0c7a690e874d67b1d4df9f7179ab9db738c4a8ee88b00
- docs/lean/statements/SP-11/ORIGINAL.md: 8e3edc4c7c6c8b388ab7bbf87bc197b76756210b19338d27398af356016aa865

## Fidelity checks

1. The source quantifies over every finite simple undirected graph with n>=1. A graph on Fin n is a relabeling of the same complete finite class; isolated vertices and the one-vertex graph remain included.

2. The matrix is real symmetric, with off-diagonal nonzero entries if and only if adjacency. Both directions of the pattern condition are retained and the diagonal remains unrestricted.

3. The requested witness has nullity at least minimum vertex degree. Natural n-rank(A) equals real kernel dimension by rank-nullity since rank(A)<=n; the imported API must still be inspected at Lean-boundary review.

4. The specification does not carry the PSD/SAP restrictions from the stronger resolution into the original unrestricted symmetric target. No connectedness or weight-sign restriction is added.

5. The complete canonical README and ORIGINAL.md agree byte for byte. The mathematical witness formulation is expressly one of the canonical formulations.

## Limits

Independent preimplementation specification fidelity review only. This does not review a Lean implementation, prove the target, revalidate the cited solution paper, or certify any kernel/Comparator execution. Later actual Lean-boundary review remains necessary.
