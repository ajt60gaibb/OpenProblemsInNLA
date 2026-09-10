# FR-01 — Polynomial-time deterministic restricted isometries with nearly linear row count

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** Uniform efficient deterministic restricted isometries are a foundational derandomization barrier with consequences for sensing, algorithms and numerical approximation.


Does a deterministic algorithm exist, with running time polynomial in $N$, which, for every pair of integers $N\geq2$ and $1\leq s\leq N$, constructs a matrix $A\in\mathbb R^{m\times N}$ satisfying
$$
m\leq C s\log^c(2N),\qquad
\|x\|_2\leq\|Ax\|_2\leq2\|x\|_2
\quad\text{whenever }x\in\mathbb R^N,\ |\operatorname{supp}(x)|\leq s,
$$
for absolute constants $C,c>0$? The algorithm must output the entries, rather than merely assert existence. As usual, one may use rational output of polynomial bit length; the fixed distortion interval permits sufficiently fine rational rounding using polynomial bit length of a construction with slack. The row bound is permitted to exceed $N$, when the identity is sufficient.

This is the deterministic construction question in the data-streams workshop report, with its original fixed-distortion convention. The sharper optimal-row question below is separately attributed and grouped here. Such matrices would give short, reproducible measurement operators with uniform control of every sparse least-squares subproblem.

## Related stronger question: optimal row count

Does a deterministic algorithm, polynomial in $N$, output for every $N\ge2$ and $1\le s\le N$ a rational matrix $B\in\mathbb Q^{m\times N}$ of polynomial bit length such that
$$
m\le C s\log(eN/s),\qquad
\tfrac12\|x\|_2^2\le\|Bx\|_2^2\le\tfrac32\|x\|_2^2
\quad\text{for all }x\in\mathbb R^N\text{ with }|\operatorname{supp}x|\le s,
$$
for an absolute $C$? This is the supplied ADD-022 quantitative formulation of the deterministic-construction gap discussed by Rao, with fixed distortion and an explicit output model. It strengthens the row target of the original question. Both targets are grouped as one entry; randomized constructions do not answer either deterministic question.

## References

1. *Open Problems in Data Streams and Related Topics*, IITK Workshop on Algorithms for Data Streams, 2006. Martin Strauss's Question 21(1), printed p. 10. [Workshop report](https://www.cse.iitk.ac.in/users/sganguly/data-stream-probs.pdf).
2. A. S. Bandeira, *Ten Lectures and Forty-Two Open Problems in the Mathematics of Data Science*, lecture notes, Open Problem 5.1 (printed p. 88), a related weaker target with sparsity about $m^{0.6}/\operatorname{polylog}N$. [Author's notes](https://people.math.ethz.ch/~abandeira/TenLecturesFortyTwoProblems.pdf).
3. A. S. Bandeira, M. Fickus, D. G. Mixon, and P. Wong, *The road to deterministic matrices with the restricted isometry property*, Journal of Fourier Analysis and Applications 19 (2013), pp. 1123–1149. Sections 1 and 4. [Paper](https://arxiv.org/abs/1202.1234).

4. S. Rao, *Satisfying the restricted isometry property with the optimal number of rows and slightly less randomness*, introduction and Theorem 1.1. [Paper](https://arxiv.org/abs/2311.07889).

## Status check — 2026-09-10

Searched “deterministic RIP polynomial time nearly optimal 2025 2026”, “restricted isometry deterministic square root bottleneck 2026”, and current explicit sensing-matrix papers. The August 2026 paper *Compressed sensing matrices from orthogonal spaces over finite fields of odd characteristic* (arXiv:2608.23062) gives particular finite-field constructions and coherence bounds, not the displayed uniform nearly linear row count. No resolution was found for either target. Rao’s v2 theorem achieves optimal rows using randomness and does not settle the stronger deterministic formulation.

**Audit update (2026-09-10):** Rechecked Rao v2: its optimal row count still uses randomness. Searches for deterministic RIP constructions through the audit date found no construction meeting either displayed target. This is a bounded literature check, not a proof that no solution exists.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
