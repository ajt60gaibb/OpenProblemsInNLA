# RA-08 — Concave-function transfer of spectral low-rank error

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because scalar concavity must control noncommuting spectral errors; community impact is reusing low-rank approximations across matrix functions.  
**Topic:** Low-rank approximation of matrix functions.  
**Last checked:** 2026-09-13

**Status:** Lean verified

<!-- colbrook-transfer -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

A rational positive definite $`6\times6`$ matrix and its exact rank-three Nyström approximation attain the optimal input spectral error but violate transformed optimality for $`f(x)=\min(x,1)`$. At $`t=1/65536`$, the output ratio is at least $`1+334583/15769728`$. Since the input excess is zero, this also excludes every finite factor $`1+C\varepsilon`$ for that scalar-concave class.

The complete target is resolved. Its former difficulty rating is historical; the original mathematical statement and source evidence are retained below.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/03_concave_transfer_counterexamples.tex), **Theorem 3.1**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/RA-08-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). That dated manuscript review was independent agent review; the separate Lean verification below certifies the full original target. External human peer review is not claimed.

<!-- /colbrook-transfer -->

## Lean proof and verification evidence — 2026-09-13

**Formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook retains authorship of the mathematical counterexample.**

The [fourteen formal exports](lean/Solution.lean) refute the complete original implication for all real symmetric PSD pairs, admissible concave functions, original dimensions/ranks/error parameters and permitted ordered eigenbases. The formal definitions use the genuine Euclidean operator norm and Mathlib continuous functional calculus. Truncations use the same selected eigenvectors, including repeated eigenspaces; admissibility allows $`f(0)>0`$. Existence of ordered spectral data and their actual CFC and norm meanings are proved.

For the unchanged six-dimensional source witness with $`t=1/65536`$ and $`f(x)=\min(x,1)`$, the input residual and both optimal tails equal $`t`$, whereas the transformed error is strictly larger. Exact compression, a degree-six polynomial minorant, genuine CFC order and a Rayleigh bound reduce the contradiction to a rational positive gap. The materially used LeanCert checker proves strict positivity in explicit kernel mode on a singleton; no interval subdivision or numerical spectral enclosure is needed. The source's larger contour-method ratio, separate Nyström sketch identity and ancillary nuclear-norm extensions are outside these fourteen exports.

Two independent statement approvals preceded implementation, and [two independent final mathematical reports](lean/README.md#review-and-checks-actually-performed) approved the complete frozen proof. The [actual Ubuntu run](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34735273999) at immutable revision [de6513d7](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/de6513d726e3f66d20730fdaef5ba99318ee7e8b/randomized-and-low-rank-approximation/RA-08/lean) passed all 17 jobs. All fourteen exports matched without definition exceptions; default-kernel replay, 59 standard-three axiom reports and both real control suites passed as a non-root user. The [independent operational audit](lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) and [coordinator acceptance](lean/verification/root-operational-2026-09-12/ROOT-CHECKS.json) bind all 613 submitted inputs and original evidence. Local Mac checks are separately identified. The [v0.4 manifest](lean/formalization.yaml), [numerical targets](lean/NUMERICAL_TARGETS.md) and [proof map](lean/PROOF_MAP.md) document the verified scope. The original mathematical statement and sources below are unchanged.

### Checked declarations, versions and reproduction

The full original target is refuted by `NLA.RA08.not_concaveSpectralTransferConjecture`. All checked declarations in namespace `NLA.RA08` are listed below; their individual contracts and source correspondence are in the [proof package](lean/README.md).

- `orderedSpectral_exists`, `orderedSpectral_semantics`
- `functionalCalculus_spectral`, `spectral_tail_norms`
- `operator_rayleigh_bound`, `witness_data`
- `witness_spectral_location`, `minorant_scalar`
- `minorant_functional_calculus`, `witness_tail_data`
- `witness_rational_certificate`, `numerical_gap_positive`
- `counterexample`, `not_concaveSpectralTransferConjecture`

The exact checked versions are:

- Lean **4.33.1**.
- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The [dependency manifest](lean/lake-manifest.json) pins all ten revisions. The successful run built the fresh project with matching official Mathlib cache objects; it does not claim to rebuild every dependency from source.

Use a clean checkout of the immutable verified revision linked above and a non-root Linux host with the [documented sandbox prerequisites](../../tools/lean/HARNESS.md). From the repository root:

```
tools/lean/bootstrap.sh /tmp/nla-ra08-check
tools/lean/selftest.sh /tmp/nla-ra08-check
tools/lean/verify.sh \
  randomized-and-low-rank-approximation/RA-08/lean \
  /tmp/nla-ra08-check
```

The verifier runs the actual controls, statement comparison, permitted-axiom checks and default-kernel replay. Its successful dated logs are linked above. A local `lake build Solution` is a separate development check.

## Problem statement

Let $`n\ge2`$, $`1\le k< n`$, and $`A,\widehat A\in\mathbb R^{n\times n}`$ satisfy $`A\succeq\widehat A\succeq0`$, where the matrices are symmetric and $`\succeq`$ is the positive semidefinite ordering. Let $`f:[0,\infty)\to[0,\infty)`$ be continuous, concave, and nondecreasing.

For $`X=\sum_{i=1}^n\lambda_iq_iq_i^T`$ with orthonormal $`q_i`$ and $`\lambda_1\ge\cdots\ge\lambda_n\ge0`$, set

```math
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\quad f(X)=\sum_{i=1}^nf(\lambda_i)q_iq_i^T,
\quad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
```

Use the same eigenvectors for the two truncations, allowing any choice within repeated eigenspaces. For every $`\varepsilon\ge0`$, does

```math
\|A-\widehat A_k\|_2\le(1+\varepsilon)\|A-A_k\|_2
```

imply

```math
\|f(A)-f(\widehat A)_k\|_2\le(1+\varepsilon)\|f(A)-f(A)_k\|_2?
```

Here $`\|\cdot\|_2`$ is the spectral norm. The question concerns every such matrix pair, function, and choice of eigendecompositions. It would allow spectral approximation guarantees to pass through a wider family of scalar functions without requiring matrix-vector products with $`f(A)`$.

## References

1. D. Persson, R. A. Meyer, and C. Musco, [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2), *SIAM Journal on Matrix Analysis and Applications* 46 (2025), 1–21. Table 1, operator-norm/concave/ordered cell, explicitly labels this open; §5 reiterates it. Equation (2) fixes the truncation convention; Theorem 2.7 proves the operator-monotone case.
2. D. Persson, T. Chen, and C. Musco, [Randomized block-Krylov subspace methods for low-rank approximation of matrix functions](https://arxiv.org/abs/2502.01888), *Linear Algebra and its Applications* 741 (2026), 32–65. Abstract and algorithmic error analysis concern specific Krylov approximants rather than this universal implication.

## Status check — 2026-09-08

Checked the first paper's latest listed arXiv v2 (2024-07-04), its 2025 journal record, Table 1, and §5. Searches for the title with “concave”, “counterexample”, “funNyström”, and 2026 found no resolution. The related 2026 Krylov paper was inspected for scope and did not supply this implication. The source's operator-norm counterexample drops the ordering assumption and therefore does not refute the statement here. No explicit reaffirmation later than the 2025 publication was located. The matrix field here follows the source's real symmetric setting, rather than the attachment's broader Hermitian convention.

## Audit — 2026-09-10

Rechecked [Table 1 and Theorem 2.7](https://arxiv.org/html/2311.14023v2): the ordered operator-monotone subclass is proved, but the larger concave class remains open. Concave-transfer and later matrix-function searches found no general resolution. The source's unordered counterexample does not refute this target.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
