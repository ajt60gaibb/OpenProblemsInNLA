# MF-16 — Uniqueness of positive definite solutions of two-letter word equations in order two

**Topic:** Structured nonlinear matrix equations.  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because uniqueness must hold for words of unbounded length despite higher-dimensional failures; specialist impact reflects the surviving two-letter, order-two setting.  
**Last checked:** 2026-09-13

**Status:** Lean verified

<!-- colbrook-matrix-functions -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The ordinary symmetric two-letter word $`XBX^{12}BX=P`$ has at least three distinct real symmetric positive definite solutions for explicit integer $`B,P`$. These are also Hermitian positive definite solutions, refuting the canonical universal uniqueness assertion in dimension two. An exact negative Jacobian determinant and two independent interval implementations certify the counterexample.

The complete target is resolved. Its former difficulty rating is historical; the original statement, references and dated audits remain below.

**Primary reference:** [complete authored PDF](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-16.pdf), [standalone TeX](../../references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-16.tex), **Theorem 1; Theorem 4 gives three certified solutions, and Theorem 3 gives a family threshold**. [Independent proof review](../../references/colbrook-matrix-functions-2026-09-11/verification/reviews/MF-16-review.md) · [Authorship and submission record](../../references/colbrook-matrix-functions-2026-09-11/README.md). That dated manuscript review was independent agent review; the separate Lean verification below certifies the full original target. External human peer review is not claimed.

<!-- /colbrook-matrix-functions -->

## Lean proof and verification evidence — 2026-09-12

**Formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook retains authorship of the mathematical counterexample.**

The [nine formal exports](lean/Solution.lean) refute the complete original universal uniqueness assertion: all finite ordinary two-letter palindromes containing $`X`$, and all complex Hermitian positive definite $`B,P`$ of order two. For the unchanged source word $`XBX^{12}BX`$ and integer matrices, the proof constructs two distinct genuine positive definite solutions. Actual written-order matrix products, complexification and every matrix-entry equality are proved. The original target and mathematical source are retained unchanged.

A single rational box of radius $`10^{-7}`$ is certified by the actual LeanCert Krawczyk checker in explicit kernel mode. Cayley–Hamilton reduces the twelfth power before interval evaluation; determinant and symmetry recover the full word equation. The soundness theorem yields an actual root, and an LDL congruence proves positive definiteness. No numerical root approximation is assumed. The source's stronger three-solution count and exponent-family threshold are outside these nine exports.

Two independent statement approvals preceded proof work, and [two independent final mathematical reports](lean/README.md#review-and-checks-actually-performed) approved the frozen proof. The [actual Ubuntu run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34735259429), at immutable revision [4e244488](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/4e24448897a088ca9e7458379add1014c5d11e0c/matrix-functions-and-stability/MF-16/lean), passed all 17 jobs. All nine exports matched without definition exceptions; default-kernel replay, 22 standard-three axiom reports and both real control suites passed as a non-root user. The [independent operational audit](lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [coordinator acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) bind all 294 submitted inputs and the original logs/artifacts. Local Mac checks are separately identified. The [v0.4 manifest](lean/formalization.yaml), [numerical targets](lean/NUMERICAL_TARGETS.md) and [proof map](lean/verification/PROOF_MAP.md) document the exact scope.

### Checked declarations, versions and reproduction

The full original target is refuted by `NLA.MF16.not_wordUniquenessConjecture`. All checked declarations in namespace `NLA.MF16` are listed below; their individual contracts and source correspondence are in the [proof package](lean/README.md).

- `word_semantics`
- `source_data`
- `twelfth_power_reduction`
- `polynomial_word_equivalence`
- `krawczyk_certificate`
- `certified_root`
- `root_to_matrix`
- `counterexample`
- `not_wordUniquenessConjecture`

The exact checked versions are:

- Lean **4.33.1**.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The [dependency manifest](lean/lake-manifest.json) pins all ten revisions. The successful run built the fresh project with matching official Mathlib cache objects; it does not claim to rebuild every dependency from source.

Use a clean checkout of the immutable verified revision linked above and a non-root Linux host with the [documented sandbox prerequisites](../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /tmp/nla-mf16-check
tools/lean/selftest.sh /tmp/nla-mf16-check
tools/lean/verify.sh \
  matrix-functions-and-stability/MF-16/lean \
  /tmp/nla-mf16-check
```

The verifier runs the actual controls, statement comparison, permitted-axiom checks and default-kernel replay. Its successful dated logs are linked above. A local `lake build Solution` is a separate development check.

## Problem statement

A word $`W(X,B)`$ is a finite product of letters from $`\{X,B\}`$. It is symmetric if its sequence of letters equals its reversal. Require at least one occurrence of $`X`$.

For every such symmetric word $`W`$ and every pair of Hermitian positive definite matrices $`B,P\in\mathbb C^{2\times2}`$, is there exactly one Hermitian positive definite matrix $`X\in\mathbb C^{2\times2}`$ satisfying

```math
W(X,B)=P?
```

Products are evaluated in the written order. Existence is known; uniqueness is the open assertion. This is the ordinary two-letter word case of the surviving order-two conjecture, with no real powers or additional fixed letters included in the statement.

## Why it matters

The question concerns whether a structured nonlinear matrix equation has a single positive definite solution branch. The elementary word $`XBX`$ connects this family with matrix geometric means and Riccati equations.

## References

- C. J. Hillar and C. R. Johnson, [Symmetric word equations in two positive definite letters](https://qualiaphile.com/files/S0002-9939-03-07163-6.pdf), *Proceedings of the American Mathematical Society* 132 (2004), 945–953, Definition 1.1, Theorem 2.2, and Conjecture 2.3. This gives the original two-letter existence and uniqueness formulation.
- S. N. Armstrong and C. J. Hillar, [Solvability of Symmetric Word Equations in Positive Definite Letters](https://arxiv.org/abs/math/0507306), *Journal of the London Mathematical Society* 76 (2007), 777–796, Theorem 1.4 and Conjecture 11.5 (p. 20 of the arXiv PDF); Remark 11.6 discusses the real order-two case.
- J. D. Lawson and Y. Lim, [Solving symmetric matrix word equations via symmetric space machinery](https://repository.lsu.edu/mathematics_pubs/611/), *Linear Algebra and its Applications* 414 (2006), 560–569. Its bounded-degree uniqueness result is summarized in Armstrong–Hillar's introduction.

## Status check

On 2026-09-08, searched the titles, “symmetric word equations”, “Conjecture 11.5”, “2 × 2”, “two-by-two”, “uniqueness”, “counterexample”, and 2025–2026. No order-two resolution was located. Armstrong–Hillar refute unrestricted uniqueness in dimensions at least three, while explicitly retaining the order-two conjecture; their special order-two theorem and known bounded-degree results do not cover every word. No recent explicit reaffirmation was found. The statement deliberately records the source-backed two-letter problem rather than presuming that the paper's comments about reducing complex matrices to real matrices cover arbitrarily many fixed letters.

## Audit — 2026-09-10

Rechecked [Armstrong–Hillar, Theorem 11.4 and Conjecture 11.5](https://arxiv.org/pdf/math/0507306). The nontrivial word $`XBX^2B^3X^2BX`$ is settled in order two, but arbitrary words remain open. Title and order-two uniqueness searches found no full resolution. Existence alone is not the reason for the partial-resolution tag.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
