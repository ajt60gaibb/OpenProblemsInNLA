# IE-19 — Sharp inverse norm bound from upper bounds on matrix entries

**Topic:** Conditioning of positive diagonally dominant linear systems.  
**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10  

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
