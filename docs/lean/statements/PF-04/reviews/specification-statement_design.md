# PF-04: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Phase: preimplementation specification. Date: 2026-09-28.
Verdict: **approve** for the exact bytes below; no mathematical changes requested.

## Reviewed source identity

- nonnegative-and-positive-factorizations/PF-04/README.md: acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a
- docs/lean/statements/PF-04/NUMERICAL_TARGETS.md: 3294326a93bf021afac3caae3349b01e6f5c23425060cbc22c8cba8c08af1e02
- docs/lean/statements/PF-04/ORIGINAL.md: acbf30a432e4ee1898661c05a9efc2f24f9ec32183da33836315b58e6c46e08a

## Fidelity checks

1. Factor(A,r) is the exact entrywise nonnegative real Gram factor with r finite columns. This is complete positivity itself and does not confuse CP with doubly nonnegative matrices.

2. The upper assertion uses width exactly 9 with zero-column padding, which is equivalent to at most 9. It quantifies over every real order-six CP matrix, including singular and zero-entry matrices and A=0.

3. The lower conjunct retains the displayed maximum-equals-nine target: one CP matrix has no factor at any natural width r<9. Together with the upper conjunct this is exactly cp-rank 9 for that witness.

4. The empty width-zero factor correctly represents the zero matrix. There is no silent default rank for non-CP matrices and no positive-definite, support-pattern or boundary restriction on the domain.

5. The complete canonical README and ORIGINAL.md agree byte for byte. The specification distinguishes the original statement from stronger witness properties in the resolution.

## Limits

Independent preimplementation specification fidelity review only. This does not review a Lean implementation, prove the target, revalidate the cited solution paper, or certify any kernel/Comparator execution. Later actual Lean-boundary review remains necessary.
