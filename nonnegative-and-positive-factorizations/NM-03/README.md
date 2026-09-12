# NM-03 — Complexity of globally optimal nonnegative rank-two approximation

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because rank two still requires a global complexity classification despite tractable special inputs; community importance comes from the basic gap between SVD approximation and constrained NMF.  
**Topic:** low-rank approximation; computational complexity  
**Last checked:** 2026-09-11  
**Status:** Solved  

<!-- colbrook-factorization -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The exact rational-input decision problem is NP-hard under polynomial-time many-one reductions, even for strictly positive symmetric positive-definite inputs. The proof supplies an inverse-polynomial additive squared-error gap and a polynomial-time rational perturbation to simple spectrum. Factors may be real, exactly as in the canonical question. NP membership and constant-relative-error hardness are not asserted.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-factorization-2026-09-11/manuscripts/NM-03_rank_two_approximation_hardness.pdf), [standalone TeX](../../references/colbrook-factorization-2026-09-11/manuscripts/NM-03_rank_two_approximation_hardness.tex), **Theorem 1; Theorem 5 and Corollary 6 strengthen the construction**. [Independent proof review](../../references/colbrook-factorization-2026-09-11/verification/reviews/NM-03-review.md) · [Authorship and submission record](../../references/colbrook-factorization-2026-09-11/README.md). Verification is independent agent review, not external human peer review or formal certification.

<!-- /colbrook-factorization -->

## Problem statement

Given an arbitrary $`X\in\mathbb Q_+^{m\times n}`$ and
$`\tau\in\mathbb Q_{\geq0}`$, determine the complexity of deciding whether

```math
\exists W\in\mathbb R_+^{m\times2},\ H\in\mathbb R_+^{2\times n}:
\quad\sum_{i=1}^m\sum_{j=1}^n
\left(X_{ij}-\sum_{k=1}^2W_{ik}H_{kj}\right)^2\leq\tau.
```

In particular, is there a deterministic algorithm polynomial in the total
binary input length, or is this decision problem NP-hard under polynomial-time
many-one reductions? This is a complexity-classification question, without
an assumption that these two outcomes exhaust the possibilities. The
factors may have real entries; only the data and threshold must be rational.
Their inner dimension is at most two, with a zero factor column permitted.

This fixes an exact decision interpretation of the literature's global
rank-two NMF optimization question. There is no promise that $`X`$ itself
has rank two. When a rank-two truncated SVD of $`X`$ is nonnegative, a best
nonnegative rank-two approximation is obtainable from it. Arbitrary input
can fall outside this tractable special case, and alternating nonnegative
least squares need not find a global optimum.

## References

Gillis, [*Nonnegative Matrix Factorization*](https://doi.org/10.1137/1.9781611976410.ch6),
§6.1.3, p. 199, Theorem 6.6 and final paragraph. Lindy, Noferini, and
Van Dooren, [*On rank-2 Nonnegative Matrix Factorizations and their variants*](https://arxiv.org/abs/2507.20612v1),
§1, with §3's suboptimal approximation and §4's ANLS initialization.

## Status check — 2026-09-10

Rechecked the [Lindy–Noferini–Van Dooren preprint](https://arxiv.org/abs/2507.20612v1) and [Noferini’s December 2025 seminar](https://www.gssi.it/seminars/seminars-2025/item/26061-nomads-seminar-rank-2-nonnegative-matrix-factorizations-and-their-variants?print=1&tmpl=component), which explicitly retains the rank-two complexity question. Inputs having a nonnegative best rank-two SVD approximation form a proved tractable subclass. Searches also found [Gouveia–Wiebe’s 2026 integer-factor problem](https://arxiv.org/abs/2602.05957); its integer factors and exact-rank input are different. The [2026 constrained Gram-feasibility hardness result](https://arxiv.org/abs/2603.19976) also has additional affine entry constraints and is not this unconstrained approximation problem. No unrestricted rational-input decision classification was located.

