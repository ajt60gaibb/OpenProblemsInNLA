# MI-22 — Lemos–Soares singular-value log-majorization

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** Controlling every partial product of singular values is challenging despite the proved eigenvalue-modulus analogue; the resulting norm comparisons are relevant across matrix analysis.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

Rational positive definite $`3\times3`$ matrices at $`t=1/8`$ violate the first singular-value inequality: the left operator norm exceeds 10900, while $`\|AB\|_2<10200`$. Exact rational root residuals and a proved operator-root error bound certify the actual principal powers.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-22-review.md) checks the full original argument and records its hash. The draft was AI-assisted; this is independent agent verification, not external human peer review or formal certification. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence — 2026-09-12

**Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance. Matthew J. Colbrook retains credit for the original negative resolution and mathematical method.

The [immutable Solution](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/26f526cf8b6232af9528b30616076dc7a2c66ac6/matrix-inequalities-and-norms/MI-22/lean/Solution.lean) proves the complete original universal statement false. All complex positive-definite inputs, all positive dimensions, every $`t\in[0,1]`$, every proper singular-value prefix and full-product equality remain in the [reviewed definitions](lean/NLA/MI22/Definitions.lean). The formal counterexample uses the disclosed exact rational adaptation $`B=DT^8D`$ and $`t=1/8`$. Its actual left operator norm exceeds 11000 and its actual $`AB`$ norm is below 10500. Colbrook's printed integer $`B`$, root-residual theorem and original 10900/10200 bounds remain informal source results; they are not claimed as this formalization's witness.

The eight checked declarations, in namespace `NLA.MI22`, are:

- `singular_values_semantics`
- `spectral_power_semantics`
- `euclidean_norm_bounds`
- `witness_rational_data`
- `witness_principal_powers`
- `witness_operator_gap`
- `counterexample`
- `not_weightedLogMajorizationConjecture`

They prove genuine Mathlib CFC powers, descending singular values with multiplicities, Euclidean operator-norm bridges, every rational witness obligation, and the actual first-prefix reversal, followed by the full negation. Two independent agents reviewed the frozen statements and complete proof. [Linux run 34720684925](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34720684925) matched all eight exports with Lean4 Comparator and replayed the solution through Lean's default kernel. The [independent operational audit](lean/verification/linux-2026-09-12/OPERATIONAL-REVIEW.md) retains the original artifacts, complete 177-input identity and both exercised sandbox/rejection control suites. All 17 internal/public [axiom reports](lean/verification/linux-2026-09-12/axiom-verification.json) use only `propext`, `Classical.choice` and `Quot.sound`; the solution contains no admissions or native execution trust.

This catalog reviewed the actual remote Linux execution and separately retained local macOS re-elaborations. Ten pinned dependency checkouts were fresh; the official Mathlib cache was used, so a complete dependency-source rebuild is not claimed. The reviews are by independent AI agents, not external human peer review or source-author endorsement. Statement referees establish correspondence with the prose; Comparator checks formal identity and kernel trust.

The proof pins **Lean 4.33.1**, [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) and [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926). LeanCert certifies only the retained strict scalar comparison $`10500<11000`$, in explicit kernel mode on a singleton. Exact matrix algebra and true root/norm proofs cover all other obligations, without interval subdivision. The [project guide](lean/README.md), [source correspondence](lean/SOURCE_CORRESPONDENCE.md), [locked dependencies](lean/lake-manifest.json) and [formalization manifest](lean/formalization.yaml) record the full scope.

From the verified revision, on an isolated non-root Linux host satisfying the [shared harness prerequisites](../../tools/lean/HARNESS.md), run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-22/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

Let $`A,B\in\mathbb C^{n\times n}`$ be positive definite and $`t\in[0,1]`$, and define $`A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2}`$. Write $`s_1(X)\ge\cdots\ge s_n(X)`$ for the singular values of $`X`$.

Does

```math
\prod_{j=1}^k s_j\bigl(A^t(A\#_tB)B^{1-t}\bigr)
\le\prod_{j=1}^k s_j(AB),\qquad 1\le k< n,
```

hold for every positive integer $`n`$, every such $`A,B,t`$, with equality of the products for $`k=n`$? This is the assertion $`s(A^t(A\#_tB)B^{1-t})\prec_{\log}s(AB)`$. The positive semidefinite version in the sources is recovered by continuous regularization $`A+\varepsilon I,B+\varepsilon I`$; endpoints in $`t`$ can be stated directly.

The question concerns the singular values of a product involving a matrix geometric mean. Such multiplicative bounds imply norm and determinant estimates useful in numerical treatment of positive definite matrices. An analogue for eigenvalue moduli has already been proved, but changes both sides of the comparison and does not answer this singular-value question.

## References

1. M. M. Ghabries, H. Abbas, B. Mourad and A. Assi, *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*, Linear Multilinear Algebra 71 (2023), 1228–1243; preprint Conjecture 1.1, p. 3, and §3. [Full preprint](https://arxiv.org/pdf/2105.13356); [published article](https://doi.org/10.1080/03081087.2022.2059050).
2. J. Shi, Z. Wang and C. Wei, *Log-majorizations of Lemos–Soares type for the metric geometric and spectral geometric means*, Ann. Funct. Anal. 17 (2026), article 53, p. 3, equation (1.2) and the following open-status statement. [Publisher](https://doi.org/10.1007/s43034-026-00532-x); [publicly indexed full-text mirror](https://www.scribd.com/document/1073369698/s43034-026-00532-x).

Status check (2026-09-10): the original arXiv record lists v1. The July 14, 2026 paper reproduces precisely this inequality as (1.2) on p. 3 and explicitly says that it is still open. The publisher PDF was inaccessible, but the indexed primary-paper text in the public mirror exposed this passage and the later discussion distinguishing the new partial results. Searches for “Lemos Soares singular log-majorization conjecture”, the exact later title, and 2025/2026 found no subsequent announced full resolution. This is a bounded search, not certification of openness.
