# IE-19 — Sharp inverse norm bound from upper bounds on matrix entries

**Topic:** Conditioning of positive diagonally dominant linear systems.  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Lean verified
**Last checked:** 2026-09-12

## Lean proof and verification evidence — 2026-09-12

**The original IE-19 conjecture is false, with a complete Lean-verified counterexample.** The [proof at revision 531941c](https://github.com/sgstepaniants/OpenProblemsInNLA/tree/531941ca0062049ccf03d3f2df418ea805ac4036/linear-systems-and-elimination/IE-19/lean) proves that the admissible matrix with diagonal entries $2$ and off-diagonal entries $1/2$, at $n=3$ and $m=\alpha=1$, has a genuine inverse with infinity norm $7/9<5/4$. The formal statement keeps the original entrywise bounds, weak diagonal dominance and all parameter quantifiers, without adding an invertibility premise. This counterexample refutes the full original lower-bound and sharp conjectures. The manuscript's additional sharp-infimum and nonattainment theorem remains informally reviewed and is outside this Lean certificate.

**Mathematical proof:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. **Lean formalization:** George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA, with AI-agent assistance.

The checked declarations in [Solution.lean](https://github.com/sgstepaniants/OpenProblemsInNLA/blob/531941ca0062049ccf03d3f2df418ea805ac4036/linear-systems-and-elimination/IE-19/lean/Solution.lean) are:

- `NLA.IE19.counterexample`
- `NLA.IE19.not_lowerBoundConjecture`
- `NLA.IE19.not_sharpConjecture`

Two independent agents [reviewed the complete proof](lean/reviews/) against the original target. [Run 34703188616](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/34703188616) executed Comparator remotely on GitHub Actions Ubuntu 24.04, matched all three formal statements and replayed the solution through Lean's default kernel. The [archived log and operational review](lean/verification/linux-2026-09-12/) record the actual run, exact source hashes, original artifact digests, and executed rejection controls for `sorry` and native-execution axioms. The [transitive axiom report](lean/verification/axioms.log) contains only `propext`, `Classical.choice`, and `Quot.sound`. The independent operational referee checked the downloaded evidence locally; it did not run Linux on the local macOS machine. The reviews are independent agent reviews, not external human peer review.

The proof pins **Lean 4.33.1**, [LeanCert 621a43d](https://github.com/alerad/leancert/tree/621a43d7cf21f87872392a01e874f2f1dbddc926) and [Mathlib 0df444a](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474). The [formalization manifest](lean/formalization.yaml) and [numerical targets](lean/NUMERICAL_TARGETS.md) describe scope and dependencies. From a checkout of the verified revision, with the documented [non-root Linux prerequisites](../../tools/lean/HARNESS.md), reproduce the check with:

```
tools/lean/bootstrap.sh /absolute/path/to/nla-lean-tools
tools/lean/selftest.sh /absolute/path/to/nla-lean-tools
tools/lean/verify.sh \
  linear-systems-and-elimination/IE-19/lean \
  /absolute/path/to/nla-lean-tools
```

<!-- colbrook-recovered -->
## Independently reviewed resolution - 2026-09-11

**Negative resolution and sharp replacement.** Section 1 gives an admissible positive symmetric strictly diagonally dominant $3\times3$ matrix with inverse infinity norm $7/9$, below the proposed comparison value $5/4$. Theorem 1 in Section 2 proves that the exact infimum over the displayed class is $1/(\alpha+m)$ for every allowed parameter choice, and strict positivity prevents attainment. The order is entrywise; stronger comparisons of dominance margins are outside the result.

**Author:** Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. [Complete manuscript](../../references/colbrook-recovered-2026-09-11/manuscripts/IE-19.pdf), [independent proof review](../../references/colbrook-recovered-2026-09-11/verification/reviews/IE-19-review.md), and [submission record](../../references/colbrook-recovered-2026-09-11/README.md). The supplied notes were reconstructed with substantial AI assistance. The 2026-09-11 review was independent agent verification, without external human peer review or formal proof-assistant certification. The later Lean verification above covers the complete negative resolution of the original conjecture. No novelty or priority claim is made.

The difficulty, importance and rating rationale below are historical assessments of the original open target. Original statements, references and dated audits are preserved.
<!-- /colbrook-recovered -->

**Rating rationale:** Challenging reflects a sharp inverse-norm inequality over a constrained matrix family; specialist impact concerns extremal conditioning for positive diagonally dominant systems.

## Problem statement

Let $n\ge3$, $m>0$, and $\alpha\ge(n-2)m$, and define

$$
S=\alpha I_n+m\mathbf1\mathbf1^T,
\qquad \mathbf1=(1,\ldots,1)^T\in\mathbb R^n.
$$

For every real symmetric matrix $J$ satisfying

$$
0<J_{ij}\le S_{ij}\quad(1\le i,j\le n),
\qquad J_{ii}\ge\sum_{j\ne i}J_{ij}\quad(1\le i\le n),
$$

does the sharp bound

$$
\|J^{-1}\|_\infty\ge
\frac{\alpha+2m(n-1)}{\alpha(\alpha+mn)}
=\|S^{-1}\|_\infty
$$

hold, with equality if and only if $J=S$? Here $\|M\|_\infty=\max_i\sum_j|M_{ij}|$. The hypotheses make $J$ nonsingular. The inequalities on entries are entrywise, not Loewner inequalities.

## Why it matters

This would give an optimal lower bound on inverse amplification for a structured family of linear systems using readily available entry bounds.

## References

- C. J. Hillar, S. Lin, and A. Wibisono, [Inverses of symmetric, diagonally dominant positive matrices and applications](https://arxiv.org/abs/1203.6812), §8, Conjecture 8.1, p. 17; the opening notation defines entrywise ordering. The parameter range for $S$ is inherited from Theorem 6.1 and the paragraph preceding Conjecture 8.1.
- C. J. Hillar and A. Wibisono, [A Hadamard-type lower bound for symmetric diagonally dominant positive matrices](https://redwood.berkeley.edu/wp-content/uploads/2018/01/hillar2015hadamard.pdf), *Linear Algebra and its Applications* 472 (2015), 135–141, §3, Conjecture 3.4 and Theorem 3.5. This follow-up settles the separate determinant conjecture, not the inverse norm claim.

## Earlier status check — 2026-09-08

On 2026-09-08, searched the original title and combinations of “Hillar”, “Lin”, “Wibisono”, “Conjecture 8.1”, “Conjecture 7.1”, “Tight bounds on the infinity norm”, and “proof”. The same inverse claim also occurs as Conjecture 7.1 in the authors' revised manuscript titled *Tight bounds on the infinity norm of inverses of symmetric diagonally dominant positive matrices*. No solution was located. The 2015 determinant resolution was checked separately. No recent explicit reaffirmation was found. The displayed parameter restriction makes explicit the diagonally dominant comparison matrix used by the source; it does not replace the conjecture's entrywise comparison by the stronger bound on diagonal dominance margins mentioned before it.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [Hillar–Lin–Wibisono](https://arxiv.org/pdf/1203.6812), §8, Conjecture 8.1: the extremizer and entrywise hypothesis agree with this statement. Searches for that conjecture and later inverse bounds found no proof of the displayed sharp inequality. Later determinant results cited above concern a different objective. The open verdict relies on this historical explicit conjecture and the bounded follow-up search.
