# IE-18 — The exact four-step amplification of restarted Anderson acceleration

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects a global maximization of a nonlinear homogeneous residual map in arbitrary dimension; community impact is an exact convergence factor for restarted Anderson acceleration.

Let $n\ge2$ and let $M\in\mathbb R^{n\times n}$ be nonzero and symmetric, with $1\notin\sigma(M)$. Put $A=I-M$. Define the positively homogeneous map
$$
R(v)=M\left(v-\frac{v^TAv}{\|Av\|_2^2}Av\right)\quad(v\ne0),\qquad R(0)=0.
$$
Two steps of restarted Anderson acceleration with memory one applied to $x=Mx+b$ propagate the residual by $R$. If $m_1,\ldots,m_n$ are the eigenvalues of $M$, is
$$
\max_{v\ne0}\frac{\|R(R(v))\|_2}{\|v\|_2}
=
\max_{i\ne j}
\left(\frac{m_im_j(m_j-m_i)}{|m_i(m_i-1)|+|m_j(m_j-1)|}\right)^2?
$$
A term with zero denominator is defined as zero: under the assumptions this can occur only when $m_i=m_j=0$.

The conjecture says that a largest four-step residual amplification is attained using only two orthogonal eigenvectors, irrespective of the dimension. It supplies an exact worst-case factor for this restart scheme, relevant to accelerated stationary solvers and multigrid.

## References

 O. A. Krzysik, H. De Sterck, and A. Smith, *Asymptotic convergence of restarted Anderson acceleration for certain normal linear systems*, SISC 47(2025), Conjecture 10, (9),(16),(24),(27) ([journal](https://doi.org/10.1137/24M1672262); [arXiv v4](https://arxiv.org/html/2312.04776v4)). Conjecture 10 states the maximum through two-eigenvector nonlinear eigenvalues; equation(24) evaluates their scalar maximum. The map formulation above also covers exact termination without an undefined $\alpha(0)$.

## Status check — 2026-09-08

 The arXiv history lists v4,12 May 2025, as latest. Its Conjecture 10 and journal abstract retain the conditional result. Searches for the paper title, “restarted Anderson Conjecture 10”, and later proof/counterexample results found no resolution. Windowed AA, GMRES(1), and restarted CG use different residual maps. The September 2026 Forsythe paper resolves the CG restart question and is not a solution claim for the map above.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

Rechecked [version 4](https://arxiv.org/html/2312.04776v4), Conjecture 10 and its surrounding discussion, against the [2025 journal record](https://doi.org/10.1137/24M1672262). The general-dimensional identity is still conjectural; the order-two case alone does not justify a substantive partial-status label. Targeted searches for this four-step amplification conjecture found no later resolution.
