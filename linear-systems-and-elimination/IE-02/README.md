# IE-02 — Is the ideal GMRES bound sharp for every Jordan block?

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Status:** Partially resolved  
**Last checked:** 2026-09-10  

**Rating rationale:** Challenging because the remaining Jordan-block minimax cases require control of multiple extremal singular vectors; specialist impact reflects a structural test case for GMRES theory.

## Problem statement

For $n\geq2$ and $\lambda\in\mathbb C\setminus\{0\}$, let $J_n(\lambda)=\lambda I+N$, where $N_{i,i+1}=1$ and all other entries of $N$ vanish. Let $\mathcal P_k=\{p\in\mathbb C[z]:\deg p\leq k,\ p(0)=1\}$. Define

$$
\psi_k(J)=\max_{\|v\|_2=1}\min_{p\in\mathcal P_k}\|p(J)v\|_2,
\qquad
\phi_k(J)=\min_{p\in\mathcal P_k}\|p(J)\|_2.
$$

Prove or disprove $\psi_k(J_n(\lambda))=\phi_k(J_n(\lambda))$ for every $1\leq k<n$. The maximum describes the slowest possible GMRES residual reduction, whereas the minimum over operator norms is the ideal bound. The familiar inequality $\psi_k\leq\phi_k$ does not answer the question. A single Jordan block is a published structural test case, not a claim about all nonnormal matrices.

## References

Tichý, Liesen, and Faber, [*On worst-case GMRES, ideal GMRES, and the polynomial numerical hull of a Jordan block*](https://etna.ricam.oeaw.ac.at/volumes/2001-2010/vol26/abstract.php?pages=453-473), ETNA 26 (2007), 453–473, §1 conjecture and subsequent special cases. Faber, Liesen, and Tichý, [*Matrix best approximation in the spectral norm*](https://arxiv.org/abs/2506.09687), published in LAA 733 (2026), §§4–5.

## Earlier status check — 2026-09-08

Searches for `Jordan block ideal GMRES equality proved 2026` and `site:arxiv.org GMRES Jordan block` found the original partial results and the 2026 general approximation paper, but no resolution of the displayed Jordan-block equality. The latter paper's doubling theorem changes the matrix and does not by itself establish this statement.

## Audit update — 2026-09-10

Rechecked the [author copy of Tichý–Liesen–Faber](https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf), especially §§3–5: Corollary 4.4 proves equality whenever $k$ divides $n$, with additional eigenvalue regimes proved elsewhere in those sections. These are substantive parts of the displayed target. The [2025/2026 approximation paper](https://arxiv.org/html/2506.09687) and targeted Jordan-block/ideal-GMRES searches did not supply the remaining cases; its doubling construction changes the input matrix.
