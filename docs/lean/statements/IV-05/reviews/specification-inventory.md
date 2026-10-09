# IV-05 independent specification review

Reviewer: OpenAI Codex agent `/root/inventory` (AI), independent of specification author `/root/statement_design`.

Phase: `specification`. Verdict: **APPROVED** for the exact mathematical target, subject to the explicit formal implementation obligations recorded below. No target implementation existed when reviewed.

Read the full canonical README and full specification; verified the complete ORIGINAL snapshot byte for byte and checked every retained source-lock hash.

The input domain preserves n>=1, rational interval endpoints with entrywise lower<=upper, and independently variable real matrix and RHS entries. The inverse-M promise is exactly invertibility plus a nonpositive off-diagonal inverse and entrywise nonnegative double inverse; its equivalent A>=0 formulation is valid only together with invertibility.

The output criterion is exact rational endpoints bounding all solutions and attained separately for each coordinate and endpoint. It is the minimal coordinate box. It neither demands all extrema arise from the same A,b nor replaces the hull by raw coordinate sets or an arbitrary enclosure.

Zero widths, mixed-sign RHS, zero entries, reducible matrices, and n=1 are retained. There is no irreducibility, strict positivity, positive-width or additional regular-AVE assumption. Behavior outside the full inverse-M promise is unrestricted.

The target includes one uniform deterministic transducer and polynomial binary running time, with rational outputs included in the semantics. Merely defining rational extrema or giving the 2n LP correspondence would omit the central algorithmic requirement.

The concrete machine/encoding/LP complexity APIs are still formal dependencies. This is an adequate exact mathematical specification for implementing them, not permission to fill the Lean statement with an arbitrary cost function or assumed solver.

This approves mathematical specification correspondence only. It does not certify a Lean implementation, the correctness of cited resolution proofs or supplemental reduction lemmas, compilation, a numerical proof, or a Linux Comparator run. The source-lock hashes were checked, but hashing a cited proof is not an independent proof audit.

The amended dependency section correctly distinguishes a concrete definition of machine execution from a proof constructing an efficient algorithm: LP, composition and reduction proofs are not prerequisites to this statement-only target. This clarification preserves the original quantifiers, analytic predicates and computational strength; it introduces no free oracle or assumed complexity theorem.

## Reviewed input hashes

- `intervals-and-absolute-value-equations/IV-05/README.md`: `09f68840d5c42b3b101532620a8900a7253f6f881bfa59ad99e80ff21c16a87c`
- `docs/lean/statements/IV-05/NUMERICAL_TARGETS.md`: `a70e3008bfa3cfae8b068fc3af690a761ee44f75bb46a2fb2a8d101ede2ff931`
- `docs/lean/statements/IV-05/ORIGINAL.md`: `09f68840d5c42b3b101532620a8900a7253f6f881bfa59ad99e80ff21c16a87c`
- `docs/lean/statements/IV-05/source-lock.json`: `d4c8f5f39f6485b54bc012165393a0ab45717911a5f7aaf4a6e1d8d87b7d8446`
