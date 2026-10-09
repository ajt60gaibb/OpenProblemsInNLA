# PF-05 independent preimplementation specification review

Reviewer: `/root/infra_audit`, an OpenAI Codex AI agent independent of the target specification author. Phase: specification. Verdict: **approve**.

I read the complete canonical README and exact specification and independently checked the proposed mathematical representation before any target Lean implementation. Infrastructure authorship does not make this reviewer an author of these problem specifications.

The matrix domain remains entrywise nonnegative real p-by-q M with ordinary real rank exactly three and PSD rank exactly two. Existence of a concrete size-two PSD factorization plus nonexistence at size one is exactly minimum positive factor size two, because the minimum in the source starts at k=1. Ordinary rank three already excludes zero dimensions without adding a new restriction.

Every row and column factor is a symmetric PSD real 2-by-2 matrix satisfying the actual trace product equation. The proposed quantification retains every fixed factorization and all zero entries, singular factors, repeated factors and zero rows or columns allowed by the source.

Feasible directions quantify real symmetric E and F, impose the exact first-order trace equation, and require one common h>0 on which every straight segment factor stays PSD for every real t in [0,h). No exact positive-time factorization is required and no arbitrary tangent-cone predicate replaces this one-sided interval condition.

Rigidity allows exactly one scalar d common to all E_i=d A_i and F_j=-d B_j. Uniqueness allows exactly one real invertible size-two S common to all factors, with the stated transpose-congruence action on A and inverse-transpose action on B. Requiring invertibility where the inverse is used is essential and is explicitly included in the specification.

The target is the equivalence of these two predicates for every such fixed factorization, not only one direction or only positive-entry matrices. Exact ranks, all weak PSD conditions, the positive h and half-open interval endpoints are preserved. Complete ORIGINAL.md bytes match the canonical README.

This approval applies only to the input bytes below. It verifies statement fidelity, not truth of the conjecture or cited resolution, human peer review, a Lean boundary, or Linux Comparator execution. The implemented definitions still require independent boundary review.

- `nonnegative-and-positive-factorizations/PF-05/README.md`: `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`
- `docs/lean/statements/PF-05/NUMERICAL_TARGETS.md`: `d5c00daa8a0bfa9b520c999b017217ab07fe9bb76b2cac6240f12f241b5db184`
- `docs/lean/statements/PF-05/ORIGINAL.md`: `f7acc0629067696f7aa2828673740e286730fb9654348b742752eb146a840f71`
