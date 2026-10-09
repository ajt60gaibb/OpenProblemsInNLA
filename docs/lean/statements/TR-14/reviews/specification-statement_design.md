# TR-14: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Phase: preimplementation specification. Date: 2026-09-28.
Verdict: **approve** for the exact bytes below; no mathematical changes requested.

## Reviewed source identity

- tensor-computations/TR-14/README.md: a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86
- docs/lean/statements/TR-14/NUMERICAL_TARGETS.md: 6c50aa83745fc3d096e08b476fb08a841ffc0fefb2cdd58511f924c49f09da17
- docs/lean/statements/TR-14/ORIGINAL.md: a6ae45a647f1cb5e057c7b1f09c5b4d99bdd5a29c25677f352f91ea0788e6d86

## Fidelity checks

1. The zero-based coordinate sum of i:Fin m to Fin n lies between 0 and m(n-1), and is exactly the original one-based sum minus m. The full complex list length m(n-1)+1 and endpoints m>=3,n>=2 are retained.

2. Ordinary factors have one independent complex vector per mode. Symmetric factors have a complex coefficient and one repeated vector. Products use no conjugation, normalization, genericity or Vandermonde restriction.

3. Both width-r predicates are upward closed by padding with zero terms. Equality of their least widths therefore implies equivalence at every r; conversely the all-r equivalence gives equality by applying it at either minimum.

4. The relevant minima exist: ordinary tensors have coordinate-basis decompositions; Hankel tensors have symmetric finite decompositions by choosing D+1 distinct complex t values, D=m(n-1), and solving the invertible Vandermonde system h_s=sum_j c_j t_j^s, yielding vectors (1,t_j,...,t_j^(n-1)). This is a correspondence argument, not a restriction on allowed decompositions.

5. At r=0 both decompositions mean the zero tensor. A symmetric summand converts to an ordinary one by absorbing its scalar into one factor (m>=3 guarantees at least one factor). The zero tensor and all exceptional h are included.

6. The complete canonical README and ORIGINAL.md agree byte for byte. The stronger all-spectrum formula in the resolution is not imposed on the original rank-equality target.

## Limits

Independent preimplementation specification fidelity review only. This does not review a Lean implementation, prove the target, revalidate the cited solution paper, or certify any kernel/Comparator execution. Later actual Lean-boundary review remains necessary.
