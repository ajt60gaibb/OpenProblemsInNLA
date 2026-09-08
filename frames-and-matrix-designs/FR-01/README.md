# FR-01 — Polynomial-time deterministic restricted isometries with nearly linear row count

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Last checked:** 2026-09-08

**Status:** source-stated open construction problem; no resolution found in screening on 2026-09-08.

Does a deterministic algorithm exist, with running time polynomial in $N$, which, for every pair of integers $N\geq2$ and $1\leq s\leq N$, constructs a matrix $A\in\mathbb R^{m\times N}$ satisfying
$$
m\leq C s\log^c(2N),\qquad
\|x\|_2\leq\|Ax\|_2\leq2\|x\|_2
\quad\text{whenever }x\in\mathbb R^N,\ |\operatorname{supp}(x)|\leq s,
$$
for absolute constants $C,c>0$? The algorithm must output the entries, rather than merely assert existence. As usual, one may use rational output of polynomial bit length; the fixed distortion interval permits constant-accuracy rounding of a construction with slack. The row bound is permitted to exceed $N$, when the identity is sufficient.

This is the deterministic construction question in the data-streams workshop report, with its original fixed-distortion convention. It does not strengthen the source to the sharper $O(s\log(N/s))$ row target. Such matrices would give short, reproducible measurement operators with uniform control of every sparse least-squares subproblem.

## References

1. *Open Problems in Data Streams and Related Topics*, IITK Workshop on Algorithms for Data Streams, 2006. Martin Strauss's restricted-isometry problem, first numbered construction question on printed p. 10, asks for a polynomial-time deterministic $s\operatorname{polylog}(N)\times N$ construction. [Workshop report](https://citeseerx.ist.psu.edu/document?doi=5394ab5bf4b66bfb52f111525d6141a3226ba883&repid=rep1&type=pdf).
2. A. S. Bandeira, *Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science*, lecture notes, Open Problem 5.1 and its surrounding discussion of explicit restricted isometries. [Author's notes](https://people.math.ethz.ch/~abandeira/TenLecturesFortyTwoProblems.pdf).
3. A. S. Bandeira, M. Fickus, D. G. Mixon, and P. Wong, *The road to deterministic matrices with the restricted isometry property*, Journal of Fourier Analysis and Applications 19 (2013), pp. 1123–1149. Sections 1 and 4 discuss the deterministic obstruction and candidate frames. [Paper](https://arxiv.org/abs/1202.1234).

## Status check — 2026-09-08

Searched “deterministic RIP polynomial time nearly optimal 2025 2026”, “restricted isometry deterministic square root bottleneck 2026”, and current explicit sensing-matrix papers. The August 2026 paper *Compressed sensing matrices from orthogonal spaces over finite fields of odd characteristic* (arXiv:2608.23062) gives particular finite-field constructions and coherence bounds, not the displayed uniform nearly linear row count. No resolution was found.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
