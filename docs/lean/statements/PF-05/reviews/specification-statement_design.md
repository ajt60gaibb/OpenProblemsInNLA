# PF-05: independent specification review

Reviewer: /root/statement_design (OpenAI Codex AI agent), independent of author /root.
Date: 2026-09-28. Phase: specification. Verdict: **approve**.
No mathematical changes requested for these exact bytes.

## Fidelity and equivalence checks

1. The domain preserves every entrywise nonnegative real p-by-q matrix of ordinary rank three and real PSD rank exactly two, and every fixed size-two factorization. Rank three excludes empty dimensions without an extra restriction.

2. PSD factorization is expressed with real symmetric PSD factors and exact trace(A_i B_j) equations. Existence at size two and nonexistence at size one exactly express minimum size two because the original minimum begins at k=1.

3. Every symmetric real direction family is quantified. The trace identity is only first order, while PSD feasibility requires one common positive h for all factors and every t in the half-open interval [0,h). Exact representation of M for positive t is correctly not required.

4. Rigidity requires a single real scalar d common to every row/column factor, with E_i=d A_i and F_j=-d B_j. It is not replaced by arbitrary infinitesimal congruences or independent scalings.

5. Uniqueness quantifies every alternative size-two PSD factorization of the same M, with one shared invertible real matrix S satisfying the exact transpose/inverse-transpose actions. Invertibility is explicit, avoiding any convention for inverse of a singular matrix.

6. The target is an equivalence for every fixed factorization. Zero entries of M, zero rows/columns, repeated and singular factors are retained; no strict positivity, positive definiteness, normalization, tangent-cone substitution or larger/smaller factor size is imposed.

7. Complete ORIGINAL.md is byte-identical to the canonical README; permanent ID, full problem statement, resolution attribution and historical context are retained.

## Reviewed inputs

- docs/lean/statements/PF-05/NUMERICAL_TARGETS.md: d5c00daa8a0bfa9b520c999b017217ab07fe9bb76b2cac6240f12f241b5db184
- docs/lean/statements/PF-05/ORIGINAL.md: f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71
- nonnegative-and-positive-factorizations/PF-05/README.md: f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71

## Limits

Independent AI-agent preimplementation specification fidelity review only. This approves these mathematical definitions and target correspondence, not any subsequent Lean implementation, proof of the target, cited-paper proof audit or kernel/Comparator run.
