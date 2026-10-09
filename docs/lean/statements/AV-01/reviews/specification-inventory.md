# AV-01 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The original decision predicate uses real solutions of the componentwise equation with exact rational input. A bijection from Fin(2^n) to the solution subtype expresses exactly 2^n distinct solutions; infinite solution sets cannot satisfy it. No finiteness, regularity, nonsingularity or sign promise is inserted.

The proposed affirmative P classification is one of the exact outcomes explicitly requested in the original classification question and is the retained resolution. It asks for one uniform finite-description deterministic machine with uniform polynomial bit-time constants, covering every valid input encoding. It neither replaces the decision task by solution enumeration nor asserts P differs from NP.

The bound uses total binary input length including dimensions and rational data. Rational/real unit-cost arithmetic and a free LP oracle are explicitly excluded. Malformed-input handling cannot remove any valid rational input.

The finite machine, encoding, step relation, output decoder and polynomial-time predicates must be implemented concretely and reviewed before a Lean target is called complete. The current draft is an adequate mathematical specification of those obligations, not an already available formal computational model. Its LP characterization and call count alone would be incomplete.

The exact equation, integer range n>=1, weak cardinality equality, and rejection of infinite solution sets match the complete canonical page. No interval numerical certificate is needed to define this proposition.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

The amended dependency section correctly distinguishes a concrete definition of machine execution from a proof constructing an efficient algorithm: LP, composition and reduction proofs are not prerequisites to this statement-only target. This clarification preserves the original quantifiers, analytic predicates and computational strength; it introduces no free oracle or assumed complexity theorem.

## Reviewed input hashes

- `intervals-and-absolute-value-equations/AV-01/README.md`: `68205f4476868847a9332d5ab294d062882302f203e6903f4da3c43f61f5f091`
- `docs/lean/statements/AV-01/NUMERICAL_TARGETS.md`: `d524be200a4238cc2b23c86eb08523bb76fe4c6accc5dac204451f2cc335b3cf`
- `docs/lean/statements/AV-01/ORIGINAL.md`: `68205f4476868847a9332d5ab294d062882302f203e6903f4da3c43f61f5f091`
- `docs/lean/statements/AV-01/source-lock.json`: `95cc1b39ee8f32841f675eb552af99cd7bb244f3e2a6f6c429345c1cca917d60`
