# MI-26 — Concave unitary-orbit subadditivity without monotonicity

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Lean verified

**Last checked:** 2026-09-12

**Rating rationale:** Removing monotonicity from a unitary-orbit comparison is challenging; spectral bounds for broad classes of matrix functions have community importance.

## Lean proof and verification evidence - 2026-09-12

**The complete original MI-26 assertion is false, with a Lean-verified counterexample.** The real-valued concave function $`f(x)=x-x^2`$ and the rational projections

```math
P=\begin{pmatrix}1&0\\0&0\end{pmatrix},\qquad
Q=\frac1{25}\begin{pmatrix}9&12\\12&16\end{pmatrix}
```

have $`f(P)=f(Q)=0`$, while the genuine spectral matrix function satisfies $`w^*f(P+Q)w=6/5>0`$ for $`w=(1,-2)^{\mathsf T}`$. Every pair of complex unitary conjugates on the right is therefore zero. The [proof at revision 81176af](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/81176af27e570b59ba1e1a0745e28944e7d57c03/matrix-inequalities-and-norms/MI-26/lean) preserves the original complex PSD inputs and complete real-valued function class.

**Mathematical counterexample and informal proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The seven checked declarations in [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/81176af27e570b59ba1e1a0745e28944e7d57c03/matrix-inequalities-and-norms/MI-26/lean/Solution.lean) are:

- `NLA.MI26.admissibleFunction_iff`: the exact original scalar concavity and value-at-zero conditions.
- `NLA.MI26.functionalCalculus_eq_spectral`: genuine CFC equals the finite spectral formula without a continuity premise.
- `NLA.MI26.functionalCalculus_congr_nonneg`: half-line extensions do not change PSD matrix functions.
- `NLA.MI26.quadratic_cfc`: the witness function gives the actual matrix polynomial $`A-A^2`$.
- `NLA.MI26.witness_data`: rational projections, exact CFC values and the positive quadratic form.
- `NLA.MI26.counterexample`: the fixed pair defeats every pair of complex unitaries.
- `NLA.MI26.not_subadditivityConjecture`: negation of the complete original assertion.

Two independent agents reviewed the [frozen statements and completed proof](lean/reviews/). [Linux run 34713045511](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34713045511) matched all seven exports with the sandboxed Comparator and replayed the solution through Lean's default kernel. The [original artifacts and independent operational audit](lean/verification/linux-2026-09-12/) retain all 118 source hashes, isolation checks and rejection controls. All 15 [transitive axiom checks](lean/verification/proof-axioms.json) use only `propext`, `Classical.choice` and `Quot.sound`. The explicit kernel LeanCert certificate $`0<6/5`$ remains in the final contradiction. These are independent agent reviews, not external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). See the [manifest](lean/formalization.yaml), [dependency pins](lean/lake-manifest.json) and [numerical targets](lean/NUMERICAL_TARGETS.md). On a documented [non-root Linux host](../../tools/lean/HARNESS.md), reproduce from the verified revision with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  matrix-inequalities-and-norms/MI-26/lean \
  /absolute/path/to/nla-lean-tools
```

The optional positive-definite variant in the informal source is outside these seven exports. The narrower globally nonnegative-valued function class is not refuted. The complete original PSD target and its historical informal proof remain below.

## Resolution — 2026-09-11

**Negative result by Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Independent proof review: PASS.**

The real-valued concave function $`f(x)=x-x^2`$ and two rational projections refute the two-unitary inequality; an explicit positive definite variant also works. The allowed condition is $`f(0)\ge0`$, without global nonnegativity or monotonicity. This does not refute the narrower nonnegative-valued function class.

The exact target is resolved. The original statement and source evidence are retained below; its former difficulty rating is historical.

**Primary manuscript:** [complete proof PDF](solution.pdf), [standalone TeX](solution.tex), Theorem 1.1 and its proof; [authorship and scope](solution.md). The [independent review](../../references/colbrook-matrix-2026-09-11/verification/reviews/MI-26-review.md) checks the full original argument and records its hash. The draft was AI-assisted; the 2026-09-11 review was independent agent verification, without external human peer review or formal certification. The later Lean verification above covers the complete original PSD target. [Submission record](../../references/colbrook-matrix-2026-09-11/README.md).

## Problem statement

For every integer $`n\ge1`$, positive semidefinite matrices $`A,B\in\mathbb C^{n\times n}`$, and real-valued concave function $`f:[0,\infty)\to\mathbb R`$ with $`f(0)\ge0`$, must there exist unitary matrices $`U,V\in\mathbb C^{n\times n}`$ such that

```math
f(A+B)\preceq Uf(A)U^*+Vf(B)V^*?
```

Here $`X\preceq Y`$ means $`Y-X`$ is positive semidefinite, $`U^*U=UU^*=I`$, and $`f(A)`$ is defined by applying $`f`$ to the eigenvalues in a spectral decomposition of $`A`$. Concavity means

```math
f(\theta x+(1-\theta)y)\ge\theta f(x)+(1-\theta)f(y)
\quad (x,y\ge0,\ 0\le\theta\le1).
```

The function is not assumed nonnegative on its entire domain; adding that assumption would change the problem. The unitaries may depend on $`A,B,f`$.

The requested inequality is an order comparison between sums of matrix functions up to changes of orthonormal basis. Such comparisons yield spectral and norm bounds for nonlinear transformations of positive semidefinite matrices.

## References

1. K. M. R. Audenaert and F. Kittaneh, *Problems and Conjectures in Matrix and Operator Inequalities*, arXiv:1201.5232v3 (2012), §2, Problem 5 and equation (11). [Full text](https://arxiv.org/html/1201.5232).
2. J.-C. Bourin and E.-Y. Lee, *Unitary orbits of Hermitian operators with convex or concave functions*, Bull. Lond. Math. Soc. 44 (2012), 1085–1102, Theorem 3.1 and Remark 3.13. [Preprint](https://arxiv.org/html/1109.2384).

Status check (2026-09-10): the two sources explicitly leave removal of monotonicity open. The published 2017 Audenaert–Kittaneh update also retains the question. Searches for “concave unitary subadditivity monotonicity”, “Bourin Lee nonmonotone concave”, and 2025/2026, together with the new arXiv:2609.05854 paper on Horn and orbit inequalities, found no stated resolution of this full function class. Recent results for nonnegative concave functions impose a stronger assumption. This is a bounded status check.
