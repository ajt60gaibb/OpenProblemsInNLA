# RA-09 — Concave-function transfer of Frobenius low-rank error

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Rating rationale:** Challenging because squared Frobenius transfer needs control of eigenvectors as well as eigenvalues; community impact is reusable low-rank approximation of matrix functions.  
**Topic:** Low-rank approximation of matrix functions.  
**Last checked:** 2026-09-13

**Status:** Lean verified

<!-- colbrook-transfer -->
## Resolution — 2026-09-11

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent Codex-agent review: PASS for the exact target.**

The ordered theorem transfers ordinary relative Frobenius residual error with no loss for the larger monotone subhomogeneous function class. Put $`B=\widehat A_k`$. Since $`0\preceq B\preceq A`$, $`\|A-B\|_F^2=\|A\|_F^2-\|B\|_F^2-2\mathop{\mathrm{tr}}\nolimits(B(A-B))\le\|A\|_F^2-\|B\|_F^2`$. Thus the original stronger trace-deficit premise implies the proved residual premise, establishing the exact canonical conclusion. All specified eigenbasis choices and zero-tail cases are covered.

The complete target is resolved. Its former difficulty rating is historical; the original mathematical statement and source evidence are retained below.

**Primary reference:** [complete authored PDF](../../references/colbrook-transfer-2026-09-11/manuscripts/02_frobenius_function_transfer.pdf), [standalone TeX](../../references/colbrook-transfer-2026-09-11/manuscripts/02_frobenius_function_transfer.tex), **Theorem 1.1, with the trace-deficit reduction above**. [Independent proof review](../../references/colbrook-transfer-2026-09-11/verification/reviews/RA-09-review.md) · [Authorship and submission record](../../references/colbrook-transfer-2026-09-11/README.md). That dated manuscript audit was independent agent review. The separate Lean verification below certifies the full original target; external human peer review is not claimed.

<!-- /colbrook-transfer -->

## Lean proof and verification evidence — 2026-09-13

**Formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. **Matthew J. Colbrook retains mathematical authorship.**

The [proof at immutable revision 3bcc8630](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/3bcc863070c037fffb1deee3f12d1cd1517727df/randomized-and-low-rank-approximation/RA-09/lean/Solution.lean) proves the complete original implication for every dimension, rank, ordered real PSD pair, allowed function, error parameter and selected ordered eigenbasis. It retains the difference-of-squared-norms premise and permits $`f(0)>0`$. Proved semantic bridges connect the definitions to the actual Frobenius norm, PSD order, spectral theorem and continuous functional calculus; ordinary and function truncations use the same selected eigenvectors. The trace-deficit reduction, selected zero eigenvalues and zero-tail cases are proved.

The full target is `NLA.RA09.concaveFrobeniusTransferConjecture`. All 17 checked exports in namespace `NLA.RA09` are:

- `frobenius_semantics`; `frobenius_orthogonal_invariance`.
- `orderedSpectral_exists`; `orderedSpectral_semantics`.
- `functionalCalculus_spectral`; `truncation_semantics`.
- `trace_deficit_reduction`; `admissible_scalar_consequences`.
- `scalar_branch_certificates`; `ordered_scalar_certificate`.
- `harmonic_constraint`; `overlap_semantics`.
- `overlap_error_expansions`; `zero_column_average`.
- `positive_tail_transfer`; `zero_tail_closure`.
- `concaveFrobeniusTransferConjecture`.

The [proof map](lean/PROOF_MAP.md) and [manifest](lean/formalization.yaml) give each contract and its original-target correspondence. Exact unbounded scalar factorizations and a sum of squares eliminate interval computations. LeanCert checks kernel trust throughout the matrix proof. The manuscript's broader function class, unordered theorem and ancillary extensions are outside these exports.

Two independent statement approvals preceded implementation; [two independent final mathematical reviews](lean/README.md#reviewed-evidence) approved the frozen proof. [Ubuntu run 34738884548](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34738884548), on 13 September 2026, matched all 17 exports without definition exceptions and replayed them through Lean's default kernel. All 49 source axiom reports permit only `propext`, `Classical.choice`, and `Quot.sound`; both actual control suites passed as a non-root user. The [independent operational audit](lean/verification/linux-2026-09-13/OPERATIONAL-REVIEW.md) and [coordinator acceptance](lean/verification/root-operational-2026-09-13/ROOT-CHECKS.json) bind the complete 524-file candidate. Local macOS development checks are recorded separately.

The checked toolchain is **Lean 4.33.1**. Dependency revisions are:

- Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.
- LeanCert: `621a43d7cf21f87872392a01e874f2f1dbddc926`.

The [Lake manifest](lean/lake-manifest.json) pins all ten dependencies. The run used a fresh project and matching official Mathlib cache objects; it did not rebuild all dependencies from source. From a clean checkout of immutable revision `3bcc863070c037fffb1deee3f12d1cd1517727df`, use a non-root Linux host with the [documented prerequisites](../../tools/lean/HARNESS.md) and run from the repository root:

```
tools/lean/bootstrap.sh /tmp/nla-ra09-check
tools/lean/selftest.sh /tmp/nla-ra09-check
tools/lean/verify.sh randomized-and-low-rank-approximation/RA-09/lean \
  /tmp/nla-ra09-check
```

These commands run the controls, statement comparison, permitted-axiom checks and default-kernel replay. A local `lake build Solution` is a separate development check. The original statement and source record below remain unchanged.

## Problem statement

Let $`n\ge2`$, $`1\le k< n`$, and $`A,\widehat A\in\mathbb R^{n\times n}`$ be symmetric with $`A\succeq\widehat A\succeq0`$. Let $`f:[0,\infty)\to[0,\infty)`$ be continuous, concave, and nondecreasing. For a positive semidefinite matrix $`X=\sum_{i=1}^n\lambda_iq_iq_i^T`$ with decreasing eigenvalues and orthonormal eigenvectors, write

```math
X_k=\sum_{i=1}^k\lambda_iq_iq_i^T,
\quad f(X)=\sum_{i=1}^nf(\lambda_i)q_iq_i^T,
\quad f(X)_k=\sum_{i=1}^kf(\lambda_i)q_iq_i^T.
```

Use the same eigenvectors for the two truncations, with any choices inside repeated eigenspaces. Is the implication

```math
\|A\|_F^2-\|\widehat A_k\|_F^2
\le(1+\varepsilon)\|A-A_k\|_F^2
```

```math
\Longrightarrow\quad
\|f(A)-f(\widehat A)_k\|_F^2
\le(1+\varepsilon)\|f(A)-f(A)_k\|_F^2
```

valid for every such input, every eigendecomposition choice, and every $`\varepsilon\ge0`$? Here $`\|M\|_F^2=\sum_{i,j}|M_{ij}|^2`$. The premise is intentionally the difference of squared norms, not merely a relative-error bound for $`\widehat A_k`$.

The problem asks whether a reusable approximation to $`A`$ provides near-optimal Frobenius approximation to a larger class of matrix functions.

## References

1. D. Persson, R. A. Meyer, and C. Musco, [Algorithm-agnostic low-rank approximation of operator monotone matrix functions](https://arxiv.org/html/2311.14023v2), *SIAM Journal on Matrix Analysis and Applications* 46 (2025), 1–21. Table 1, Frobenius/concave/ordered cell and its asterisk; Theorem 2.5 supplies the stronger premise being extended, and §5 explicitly leaves the concave case open. Equation (2) specifies truncation.
2. D. Persson, T. Chen, and C. Musco, [Randomized block-Krylov subspace methods for low-rank approximation of matrix functions](https://arxiv.org/abs/2502.01888), *Linear Algebra and its Applications* 741 (2026), 32–65. This related work analyzes particular randomized Krylov constructions.

## Status check — 2026-09-08

Checked the source's latest listed arXiv v2 (2024-07-04), 2025 journal record, Table 1, Theorem 2.5, and §5. Searches combining the title, “concave”, “Frobenius”, “counterexample”, “funNyström”, and 2026 found no resolution. The related 2026 Krylov paper does not establish the universal ordered-pair implication. No explicit reaffirmation later than the 2025 publication was located. The source's nuclear-norm counterexample and its unordered Frobenius example do not answer this target. Unlike the spectral-error question, this statement concerns squared Frobenius error and a stronger premise; these are distinct explicitly marked open cells in the source table.

## Audit — 2026-09-10

Rechecked [Table 1 and Theorem 2.5](https://arxiv.org/html/2311.14023v2): operator-monotone functions satisfy this stronger-premise implication, while general concave functions remain open. Frobenius/concavity and later matrix-function searches found no resolution. The difference-of-squared-norms premise is essential.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
