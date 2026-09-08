# NR-01 — Exact nonnegative rank of regular polygon slack matrices

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** open; checked 2026-09-08  
**Area:** structured nonnegative matrix factorization  
**Last checked:** 2026-09-08  

## Context and notation

All factorizations are over the real numbers. For
$X\in\mathbb R_{\ge0}^{m\times n}$, define

$$
\operatorname{rank}_+(X)=\min\{r\ge0:X=WH,\quad
W\in\mathbb R_{\ge0}^{m\times r},\ H\in\mathbb R_{\ge0}^{r\times n}\}.
$$

## Problem statement

For each integer $n\ge3$, define the $n\times n$ nonnegative matrix

$$
S_n(i,j)=\cos(\pi/n)-\cos\bigl((2i+1-2j)\pi/n\bigr),
\qquad 0\le i,j<n.
$$

It is the slack matrix obtained from the vertices of the regular $n$-gon on
the unit circle and its supporting facet inequalities.

### Question

With $k=\lceil\log_2 n\rceil$, is it true for every $n\ge3$ that

$$
\operatorname{rank}_+(S_n)=
\begin{cases}
2k-1,&2^{k-1}<n\le 2^{k-1}+2^{k-2},\\
2k,&2^{k-1}+2^{k-2}<n\le2^k?
\end{cases}
$$

## References

Arnaud Vandaele, Nicolas Gillis, François Glineur, and Daniel
Tuyttens, [*Heuristics for Exact Nonnegative Matrix Factorization*](https://arxiv.org/html/1411.7245),
Journal of Global Optimization **65** (2016), 369–400, §6.2, Conjecture 2.
Vandaele, Gillis, and Glineur,
[*On the Linear Extension Complexity of Regular n-gons*](https://arxiv.org/abs/1505.08031),
Linear Algebra and its Applications **521** (2017), 217–239, proves the
corresponding upper bound. Nicolas Gillis,
[*Nonnegative Matrix Factorization*](https://orbi.umons.ac.be/bitstream/20.500.12907/42337/1/NMFbook_SIAM_reprint.pdf),
SIAM, 2020, §3.6.3.4, p. 90.

## Status evidence

Baeckelant, Vandaele, and Gillis,
[*Computing Lower Bounds on the Nonnegative Rank via Non-Convex Optimization Solvers*](https://arxiv.org/html/2605.14058v2),
revised July 6, 2026, Appendix A.2, still identifies sharpness as conjectural.
Searches for the conjecture and regular-polygon nonnegative ranks in 2025–2026
found no subsequent resolution. The family is counted once.
