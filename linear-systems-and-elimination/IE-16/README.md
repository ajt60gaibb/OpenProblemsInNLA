# IE-16 — A sharp subset bound for worst-case normal GMRES

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** explicit conjecture; no later resolution located  
**Last checked:** 2026-09-08

Let $L\subset\mathbb C\setminus\{0\}$ consist of $n\ge3$ distinct points. For a nonempty $S\subseteq L$, define
$$
M_k(S)=\min_{p\in\mathbb C[z],\ \deg p\le k,\ p(0)=1}\max_{z\in S}|p(z)|.
$$
Is it true, simultaneously for every such $L$ and $1\le k\le n-2$, that
$$
M_k(L)\le\frac4\pi\max_{S\subseteq L,\ |S|=k+1}M_k(S)?
$$
The constant is required to be independent of dimension, degree, and the locations of the points.

For a normal matrix with spectrum $L$, $M_k(L)$ is the largest relative residual norm attainable at GMRES step $k$, over unit initial residuals. The smaller-set quantities have explicit formulas through Lagrange interpolation. The question therefore asks for a sharp, dimension-independent certificate of worst-case convergence using small subsets of the spectrum. It is distinct from equality of ideal and worst-case GMRES for a nonnormal Jordan block (IE-02).

## References

 J. Liesen and P. Tichý, *The worst-case GMRES for normal matrices*, BIT 44 (2004), 79–98, conjecture (3.16), pp. 91–92, and Appendix ([author copy](https://page.math.tu-berlin.de/~liesen/Publicat/LieTic04.pdf)). Their *A min-max problem on roots of unity*, TU Berlin Preprint 28-2003, conclusion (9.1), proves selected roots-of-unity cases and sharpness of $4/\pi$ ([university record](https://doi.org/10.14279/depositonce-14263)). Their survey *Convergence analysis of Krylov subspace methods*, GAMM-Mitteilungen 27 (2004), discussion after (11), restates the conjecture ([author copy](https://page.math.tu-berlin.de/~liesen/Publicat/LiTiGAMM.pdf)).

## Status check — 2026-09-08

 Searched the original title with “conjecture”, “4/pi”, “4/π”, “proof”, “counterexample”, and 2025–2026; checked the authors' current publication lists. The later Jordan-block papers concern a different conjecture. No resolution or recent explicit reaffirmation of this particular bound was located; its open-status evidence is historical and bounded.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
