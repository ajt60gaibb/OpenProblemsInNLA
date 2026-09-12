# RA-07 — Convexity of the expected error of volume-sampled column subsets

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because the required second-difference inequality goes beyond standard log-concavity; community impact is understanding average column-selection and Nyström error.  
**Last checked:** 2026-09-12

**Status:** Lean verified

## Lean proof and verification evidence — 2026-09-12

**The complete original discrete-convexity assertion is Lean verified.** The [proof at revision bf144a8](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean) covers every $`n\geq3`$, strictly positive real tuple and $`2\leq j\leq n-1`$, including repeated eigenvalues and both endpoint indices, without ordering or factorization assumptions.

**Mathematical proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The actual generating-polynomial derivative of order $`j-1`$ has $`n-j+1\geq2`$ positive reciprocal-root factors $`\mu_a`$, with multiplicity. The proof derives

```math
f(j-1)-2f(j)+f(j+1)
=\frac{2\sum_{a< b}\mu_a\mu_b(\mu_a-\mu_b)^2}
{s_1(s_1^2-s_2)}\geq0,
\qquad s_r=\sum_a\mu_a^r,
```

including strict positivity of the denominator. The six [checked exports](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/bf144a8ea84992d64f79f4425b18352843376286/randomized-and-low-rank-approximation/RA-07/lean/Solution.lean), each with prefix `NLA.RA07.`, are:

- `elementary_values`: actual subset-sum conventions and positivity.
- `generating_derivative_values`: actual coefficients and factorial-scaled derivatives.
- `positive_derivative_factorization`: exact degree, real splitting and every root multiplicity.
- `power_sum_certificate`: positive denominator and exact nonnegative pair identity.
- `second_difference_certificate`: that identity for every original ratio and index.
- `errorSequence_convex`: the complete affirmative canonical theorem.

Separate pairs of independent agents approved the [statements and proof](lean/reviews/). [Linux run 34715563781](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34715563781) matched all six exports with the sandboxed Comparator and replayed the solution in Lean's default kernel. The [operational audit and original artifacts](lean/verification/linux-2026-09-12/) bind 123 inputs and the isolation/rejection controls. Twelve transitive axiom checks use only `propext`, `Classical.choice` and `Quot.sound`. No external human peer review is claimed.

The pins are **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). LeanCert audits kernel trust; there is no numerical interval certificate or approximate root computation. See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [exact targets](lean/NUMERICAL_TARGETS.md). From the verified revision on a [non-root Linux host](../../tools/lean/HARNESS.md):

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  randomized-and-low-rank-approximation/RA-07/lean \
  /absolute/path/to/nla-lean-tools
```

The source's additional monotonicity, index-one, sampling-expectation and application claims are outside these six exports. The complete original scalar convexity target and its historical informal proof remain below.

<!-- colbrook-transfer -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The sequence $`(j+1)e_{j+1}/e_j`$ is decreasing and discretely convex for every positive spectrum, including both endpoints. The exact second-difference certificate proves the full canonical conjecture.

The complete target is resolved. Its former difficulty rating is historical; the original mathematical statement and source evidence are retained below.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/01_volume_sampling_convexity.tex), **Theorem 1.1**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/RA-07-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). The 2026-09-11 verification was independent agent review, without external human peer review or formal certification. The later Lean verification above covers the complete canonical scalar convexity target.

<!-- /colbrook-transfer -->

For $`n\geq3`$ and positive real numbers $`\lambda_1,\ldots,\lambda_n`$, let

```math
e_j(\lambda)=\sum_{\substack{S\subseteq\{1,\ldots,n\}\\|S|=j}}
\prod_{i\in S}\lambda_i,
\qquad e_0=1,\quad e_{n+1}=0.
```

Define $`f(j)=(j+1)e_{j+1}(\lambda)/e_j(\lambda)`$ for $`1\leq j\leq n`$. Is $`f`$ discretely convex, that is,

```math
f(j-1)-2f(j)+f(j+1)\geq0
\qquad(2\leq j\leq n-1),
```

for every such $`n`$ and positive tuple $`\lambda`$?

For a matrix $`A`$ with positive eigenvalues $`\lambda_i`$ of $`A^TA`$, sample a set $`S`$ of $`j`$ columns with probability proportional to $`\det(A_S^TA_S)`$. Its expected squared Frobenius projection error is

```math
\mathbb E\|(I-P_{A_S})A\|_F^2=f(j),
```

where $`P_{A_S}`$ is the orthogonal projector onto the selected column span. Thus the conjecture asserts a diminishing marginal improvement in the average reconstruction error of these fixed-size determinantal samples. It is distinct from optimizing a worst-case approximation factor over all matrices with a prescribed spectrum.

## References

1. M. Dereziński, R. Khanna, and M. W. Mahoney, *Improved guarantees and a multiple-descent curve for Column Subset Selection and the Nyström method*, NeurIPS 2020, arXiv:2002.09073. Section 5, Conjecture 1 is exactly the discrete-convexity statement. [Paper](https://arxiv.org/abs/2002.09073).
2. A. Deshpande, L. Rademacher, S. S. Vempala, and G. Wang, *Matrix Approximation and Projective Clustering via Volume Sampling*, Theory of Computing 2 (2006), Article 12, pp. 225–247. See the volume-sampling matrix approximation results. [Paper](https://theoryofcomputing.org/articles/v002a012/).

## Status check — 2026-09-08

Searched “Derezinski Khanna Mahoney Conjecture 1 convexity”, “elementary symmetric ratio $`k+1`$ convexity DPP”, and the exact 2020 paper title with 2025/2026. Checked the current arXiv record. No proof or counterexample was found. Standard Newton inequalities imply other ratio inequalities but are not cited as a resolution of this second-difference inequality.

## Audit — 2026-09-10

Rechecked [Dereziński–Khanna–Mahoney, §5, Conjecture 1](https://arxiv.org/html/2002.09073); the current record remains v3 of December 2020. Volume-sampling convexity and elementary-symmetric-ratio searches found no resolution. This remains historical explicit conjecture evidence, supplemented by a bounded follow-up search.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
