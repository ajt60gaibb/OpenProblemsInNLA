# IE-22 — Optimal uniform row-deletion singular-value constant

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Open  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging reflects an optimal uniform extremum over matrices and deleted row sets; community impact is a sharp robustness limit for row-sampling methods.

## Problem statement

Fix $0<\theta<1$. For a real $m\times n$ matrix $A$ with every row of Euclidean norm one, put

$$
s_\theta(A)=\min_{S\subseteq\{1,\ldots,m\},\ |S|=\lfloor\theta m\rfloor}
\min_{\|x\|_2=1}\|A_Sx\|_2,
\qquad
M_{m,n}(\theta)=\sup_{\|a_i\|_2=1}\sqrt{\frac nm}\,s_\theta(A).
$$

Here $a_i$ is row $i$ of $A$, and $A_S$ contains exactly the rows indexed by $S$.

Determine the sharp asymptotic upper constant for $M_{m,n}(\theta)$ as $n\to\infty$ and $m/n\to\infty$. In particular, is it

$$
c_\theta=\left(\frac1{\sqrt{2\pi}}\int_{-a_\theta}^{a_\theta}t^2e^{-t^2/2}\,dt\right)^{1/2},
\qquad
\mathbb P(|G|\le a_\theta)=\theta,\quad G\sim N(0,1)?
$$

Precisely, the proposed uniform inequality asks whether, for every $\varepsilon>0$, there exist integers $N$ and $R$ such that

$$
M_{m,n}(\theta)\le c_\theta+\varepsilon
\quad\text{whenever }n\ge N\text{ and }m/n\ge R,
$$

and whether no smaller constant has this property. The supremum and quantifiers specify the source's uniform $1+o(1)$ bound; the floor convention handles row-count integrality.

## Connection to numerical linear algebra

This asks how well any unit-row linear system can retain its smallest singular value under worst-case row removal, a geometric constraint on robust iterative solvers.

## References

1. S. Steinerberger, *Quantile-based Random Kaczmarz for corrupted linear systems of equations*, Information and Inference **12**(1) (2023), 448–465, §2.3, the third question immediately after equation (8). [Published paper](https://doi.org/10.1093/imaiai/iaab029). [Author preprint](https://arxiv.org/abs/2107.05554), v1, §2.3, paragraph following $(\diamond)$.
2. E. Battaglia, J.-F. Cai, J. Chen, A. Ma, D. Needell, and T. Wu, *Quantile Randomized Kaczmarz for Streaming Linear Systems with Massart Noise*, arXiv:2608.27968v1 (2026), §1.1 (background on the same restricted-singular-value heuristic and the different streaming model), §5. [Preprint](https://arxiv.org/abs/2608.27968).

## Earlier status check — 2026-09-08

Checked the published question and latest arXiv records on 2026-09-08. Targeted searches for “Steinerberger subsingular”, “small subsingular values”, “quantile Kaczmarz optimal constants”, “unit rows smallest singular value”, and 2025/2026 variants found no resolution of the all-matrices extremum. Recent streaming Kaczmarz guarantees do not supply this universal extremal inequality. The random-ensemble limit in the same source is a related but distinct question: it specifies a random construction, whereas this question optimizes over all unit-row matrices. Openness remains subject to the limits of this search.

## Audit update — 2026-09-10

Rechecked Steinerberger's [primary formulation](https://arxiv.org/pdf/2107.05554), §2.3. Searches for the optimal row-deletion constant and quantile-Kaczmarz follow-ups found no proof of this extremal value. The new [Cai–Chen–Ma–Wu paper](https://doi.org/10.1137/25M1785678), SIAM J. Matrix Anal. Appl. 47 (2026), 802–823, proves a tight QRK subsample-size result, not the universal matrix constant asked for here.
