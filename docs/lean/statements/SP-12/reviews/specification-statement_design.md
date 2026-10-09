# SP-12: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Phase: preimplementation specification. Date: 2026-09-28.
Verdict: **approve** for the exact bytes below; no mathematical changes requested.

## Reviewed source identity

- eigenvalues-and-inverse-problems/SP-12/README.md: cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1
- docs/lean/statements/SP-12/NUMERICAL_TARGETS.md: 6dae7d486ecaeab1903b31e816e34f57fef417ef15627574f4c4a307b902cae7
- docs/lean/statements/SP-12/ORIGINAL.md: cdc8003bc5160604408ce6b95c344a4ea1b9bfbf8af0f99ae1e8e016648d53e1

## Fidelity checks

1. The universal finite simple graph domain includes n=1, disconnected graphs and isolated vertices. A real symmetric witness has the exact off-diagonal pattern, PSD, SAP and nullity at least chromatic number minus one.

2. SAP is faithfully expanded: every symmetric real X with ordinary AX=0, coordinate products A_ij X_ij=0, and diagonal X_ii=0 must vanish. The identity Hadamard product is correctly interpreted as zero diagonal.

3. Chromatic number is concretely the least number of colors admitting a proper Fin n to Fin c coloring. This set is nonempty by the identity coloring; since n>=1 its minimum is at least 1, so natural subtraction by 1 preserves the target.

4. The existential witness is equivalent to the source maximum-nu bound: possible nullities are natural numbers <=n, and the class is nonempty (a strictly diagonally dominant SPD matrix with graph off-diagonal pattern is invertible and therefore SAP). No arbitrary invariant is supplied as an input.

5. The complete canonical README and ORIGINAL.md agree byte for byte. Imported rank and PSD definitions require fresh inspection on the implemented Lean boundary.

## Limits

Independent preimplementation specification fidelity review only. This does not review a Lean implementation, prove the target, revalidate the cited solution paper, or certify any kernel/Comparator execution. Later actual Lean-boundary review remains necessary.
