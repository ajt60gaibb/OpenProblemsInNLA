# MI-21 — Freewan–Hayajneh inequality for sums of weighted geometric means

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified
**Last checked:** 2026-09-12

**Rating rationale:** The coupled power and weight parameters make extension beyond the proved cases challenging; positive definite aggregation and matrix-function estimates give community relevance.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

Two rational positive definite $`2\times2`$ summands with $`s=t=1/2`$, $`r=2`$ and aggregate matrices $`A=B=I`$ violate the operator-norm inequality for every $`p>0`$. The left side has eigenvalue $`1351000/1350907>1`$, while the right side is one.

The exact target is resolved. The complete negative answer now has [Lean proof and verification evidence](#lean-proof-and-verification-evidence--2026-09-12). The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-21-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The subsequent Lean verification below covers the complete negative answer. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Lean proof and verification evidence — 2026-09-12

**Mathematical counterexample:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The [proof at revision 06ade65](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/06ade659dee260a18b79ce638383bf0a49125ecf/matrix-inequalities-and-norms/MI-21/lean) establishes the full negative answer. It preserves every original complex-matrix, dimension, parameter and unitarily invariant norm quantifier. The witness uses the genuine Euclidean operator norm, separately proved admissible, and actual spectral powers and weighted geometric means. All input positivity and numerical identities are proved. A nonzero eigenvector gives a strict norm violation for every $`p>0`$; it does not replace the norm definition.

[Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/06ade659dee260a18b79ce638383bf0a49125ecf/matrix-inequalities-and-norms/MI-21/lean/Solution.lean) exports:

- `NLA.MI21.operatorNorm_isUnitaryInvariant`: the actual complex Euclidean operator norm satisfies every stipulated norm and two-sided unitary-invariance property.
- `NLA.MI21.counterexample`: all admissible witness hypotheses, genuine functional-calculus identities and the strict norm violation for every positive outer parameter.
- `NLA.MI21.not_geometricMeanNormConjecture`: negation of the complete original universal assertion.

Two independent agents [reviewed the frozen statements and complete proof](lean/reviews/) against the original target. [Linux run 34709291489](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34709291489) executed the actual sandboxed Lean4 Comparator on GitHub Actions Ubuntu 24.04, matched all three declarations and replayed the solution through Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) retain the complete 81-input source identity, artifact digests and successful sandbox, raw-kernel and axiom-rejection controls. All 11 internal/public [transitive axiom reports](lean/verification/proof-axioms.json) use only `propext`, `Classical.choice` and `Quot.sound`. This catalog reviewed the remote Linux execution; local macOS re-elaborations are recorded separately. These are independent AI-agent reviews, not external human peer review or source-author endorsement. The statement referees establish correspondence with the original prose; Comparator checks formal identity and kernel trust.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474), with [all dependency revisions locked](lean/lake-manifest.json). A generic positive-square-root argument identifies the actual geometric means from two exact Riccati certificates. One kernel-mode LeanCert point certificate proves the strict scalar gap; no interval subdivision or numerical matrix-root approximation is needed. The [formalization manifest](lean/formalization.yaml), [numerical obligations](lean/NUMERICAL_TARGETS.md) and [project guide](lean/README.md) record scope and reproduction. The narrower parameter regimes already proved in the literature are not contradicted.

From the verified proof revision, on an isolated non-root Linux host meeting the [shared harness prerequisites](../../tools/lean/HARNESS.md), run:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-21/lean \
  /absolute/path/to/nla-lean-tools
```

## Problem statement

For positive definite matrices, define

```math
A\#_tB=A^{1/2}(A^{-1/2}BA^{-1/2})^tA^{1/2}.
```

Is the following true for all positive integers $`m,n`$, all $`A_i,B_i\in\mathbb C^{n\times n}`$ positive definite, all $`t\in[0,1]`$, and all real $`s,r,p>0`$ with $`sr\ge1`$? Set $`A=\sum_iA_i`$, $`B=\sum_iB_i`$. For every unitarily invariant norm on $`n\times n`$ matrices, does

```math
\left\|\sum_{i=1}^m(A_i^s\#_tB_i^s)^r\right\|
\le
\left\|\left(A^{(1-t)srp/2}B^{tsrp}A^{(1-t)srp/2}\right)^{1/p}\right\|
```

hold? Here all real powers of positive definite matrices use spectral functional calculus, and unitary invariance means $`\|UXV\|=\|X\|`$ for unitary $`U,V`$.

The conjecture controls the norm of a sum of nonlinear positive definite matrix means using only sums of the input matrices. It is relevant to aggregation and interpolation of positive definite data and to estimates for algorithms involving matrix powers. The full weighted statement is one problem; its individual parameter cases are not separate entries.

## References

1. S. Freewan and M. Hayajneh, *On a conjecture related to the geometric mean and norm inequalities*, Math. Inequal. Appl. 27 (2024), Conjecture 3, p. 195. [Publisher PDF](https://files.ele-math.com/articles/mia-27-15.pdf).
2. S. Freewan and M. Hayajneh, *Norm inequalities involving geometric means*, arXiv:2401.00337v1, Conjecture 1.4 and the main theorem. [Preprint](https://arxiv.org/abs/2401.00337).

Status check (2026-09-10): the current arXiv record lists v1, December 30, 2023. Its theorem treats $`t=1/2`$, $`s\ge2`$, $`r\ge1`$, $`p>0`$, $`rp\ge1`$; the abstract explicitly identifies this as a partial answer to the weighted conjecture. The original publisher text and the later preprint statement were compared. Searches for both exact titles, the authors and “weighted geometric mean conjecture”, including 2025/2026, found no full proof or counterexample. Openness is subject to this search limit.
