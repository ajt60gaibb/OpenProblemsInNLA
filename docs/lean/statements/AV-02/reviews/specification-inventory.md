# AV-02 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The promise quantifies over every real diagonal perturbation in the closed cube [-1,1]^n and requires nonzero determinant. Only diagonal entries vary. Input dimensions, rational A and strictly positive rational threshold remain in the original domain.

The norm is explicitly the Euclidean induced operator norm. The >= threshold includes equality. Replacing the maximum by an existential perturbation is justified under the promise by continuity of inverse/norm on the compact cube; an arbitrary totalized inverse at a singular point cannot create legal yes instances.

The computational conclusion preserves promise-safe polynomial-time Turing NP-hardness. It quantifies over NP languages and reductions against every oracle correct on promised instances, and requires legal queries throughout every such run. It does not assume efficient promise recognition or claim P differs from NP.

The stronger many-one MAX-CUT construction is identified as proof data, not substituted for the requested complexity predicate. In particular an unconstrained function named NPHard or a correctness equivalence without polynomial construction/NP semantics would fail this specification.

A concrete binary Turing, NP and oracle-reduction implementation remains required before a complete Lean boundary. The spec accurately states that dependency; this approval certifies the mathematical target correspondence rather than the missing formal infrastructure or correctness of the archived reduction proof.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

The amended dependency section correctly distinguishes a concrete definition of machine execution from a proof constructing an efficient algorithm: LP, composition and reduction proofs are not prerequisites to this statement-only target. This clarification preserves the original quantifiers, analytic predicates and computational strength; it introduces no free oracle or assumed complexity theorem.

## Reviewed input hashes

- `intervals-and-absolute-value-equations/AV-02/README.md`: `c3e81826d271c719b61c0b2ba102206e24d2452a4684511d87cbacb1e7224828`
- `docs/lean/statements/AV-02/NUMERICAL_TARGETS.md`: `26dba9081ffffa9d4b46d2feee2749992fb659bc2e9d12afdaeabb0a672da7da`
- `docs/lean/statements/AV-02/ORIGINAL.md`: `c3e81826d271c719b61c0b2ba102206e24d2452a4684511d87cbacb1e7224828`
- `docs/lean/statements/AV-02/source-lock.json`: `dd1a71dcad5909fd0c55bf81d67f24dfd83f91f0a3d3ee8f59c179b779530f50`
