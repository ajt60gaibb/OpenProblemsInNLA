# IE-22 independent specification review

Reviewer: OpenAI Codex AI agent `/root/inventory`, independent of specification author `/root/infra_audit` and prospective Lean author `/root`.

Phase: `specification`. Verdict: **APPROVE** before implementation.

The complete canonical README equals ORIGINAL.md byte for byte. The target contains both the original eventual-uniform upper-bound clause and the exact no-smaller-constant clause for c=sqrt(h), without inserting a stronger manuscript rate or the defective old sequence extension.

The same concrete infimum over row subsets and Euclidean unit vectors preserves the original variational least singular value, including rank deficiency and k=0. Every row of every matrix in the deterministic supremum is required to have squared Euclidean norm one. The supremum includes repeated rows, arbitrary correlations and negative entries and has no random, generic or full-rank assumption.

For positive m,n the matrix family is nonempty by repeating the first coordinate vector; the quadratic row-energy bound gives 0<=sSq<=m and consequently M<=sqrt(n). Thus the real supremum is finite and nonempty, not a default value. The exact placement sqrt(n/m)*sqrt(sSq) preserves the original normalization.

The quantile and Gaussian integral exactly match the original constant, with a unique positive a for every theta in (0,1). There is no numerical replacement or uninterpreted h. IE22 imports no probability model for its matrices; Gaussian probability appears only to define the scalar quantile.

Upper(theta,c) quantifies every epsilon>0, then chooses N,R before every positive n,m. The natural condition R*n<=m is equivalent to the original ratio threshold for n>0; nonnegative natural thresholds are equivalent to existential integer thresholds by increasing any negative threshold. The thresholds may depend on theta,c,epsilon but never on the chosen dimensions or matrix.

Optimality is forall cprime<c, not Upper(theta,cprime). Its negation expands to one positive violating tolerance for each smaller candidate, followed by every threshold pair and suitable dimensions. It does not incorrectly require failure at every tolerance. Negative candidates remain covered, and a single sequence or fixed-size lower bound does not replace this complete clause.

The old SupremumConverges omission of n_j->infinity is correctly excluded. At n=1, unit rows give M=sqrt(floor(theta*m)/m)->sqrt(theta), which differs from sqrt(h_theta) because h_theta=theta-2*a*phi(a)<theta. The new target retains the canonical two eventual-uniform clauses and the manuscript’s stronger results only as credited context.

This approves exact specification correspondence and the stated concrete definitions, not a resolution proof, formal derivation of all correspondence lemmas, compilation or Linux Comparator execution. Final live/frozen definitions and every local import require independent boundary review. No numerical quadrature or simulation is necessary to state these targets.

## Reviewed input hashes

- `linear-systems-and-elimination/IE-22/README.md`: `273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344`
- `docs/lean/statements/IE-22/NUMERICAL_TARGETS.md`: `f42039df583dc45692c44053fbb69dcf713c04296be55a2b3b3972b2a7a92ece`
- `docs/lean/statements/IE-22/ORIGINAL.md`: `273ce377e8de3f575be53104f156f0436ffb571a3a464bb5d5693c0aa510c344`
- `references/colbrook-recovered-2026-09-11/manuscripts/IE-21-22.tex`: `31a1949c07f63408538f04e3803d90e8d3d0c3d1e47dc89a2ffa5a04ef4f3880`
