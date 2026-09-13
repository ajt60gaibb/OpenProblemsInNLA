# IE-16 — A sharp subset bound for worst-case normal GMRES

**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Solved
**Last checked:** 2026-09-12

**Historical rating rationale:** Challenging reflects extending a discrete real approximation principle to complex spectra with a sharp constant; community impact concerns usable worst-case GMRES bounds for normal matrices.

## Resolution: negative, 12 September 2026

**Author:** Sidney Holden, Center for Computational Biology, Flatiron Institute, Simons Foundation. [Verified affiliation and submission record](../../references/holden-ie16-2026-09-12/README.md).

[Theorem 1.1, proved in Sections 2-3 of the manuscript](solution.pdf) disproves the displayed universal inequality. With $`\omega=e^{2\pi i/3}`$, take the nine distinct nonzero points $`L=\{\omega^a+10^{-3}\omega^b:0\le a,b\le2\}`$ and $`k=4`$. Then

```math
M_4(L)=\frac{3003003000}{1001003001001}>\frac{299}{100000},
\qquad \max_{S\subseteq L,\ |S|=5}M_4(S)<\frac{23}{10000}.
```

The ratio is therefore greater than $`13/10>4/\pi`$. Here $`n=9`$ and $`1\le4\le n-2`$, so all original assumptions and quantifiers are addressed by this counterexample. Theorem 1.2 (Sections 4-5) additionally proves that no finite dimension-independent replacement constant exists. The finite counterexample alone settles IE-16 negatively; no case of the original universal truth question remains open.

The complete proof passed a separate [independent Codex AI-agent informal audit](../../references/holden-ie16-2026-09-12/INDEPENDENT-REVIEW.md). The supplied exact-arithmetic verifier passed all 126 subset checks, and reviewer-written rational checks passed independently. This is not external human peer review or formal verification. No Lean verification was performed. [Proof source](solution.tex) · [Exact verifier and certificates](../../references/holden-ie16-2026-09-12/submitted/README.md).

## Original problem (retained)

Let $`L\subset\mathbb C\setminus\{0\}`$ consist of $`n\ge3`$ distinct points. For a nonempty $`S\subseteq L`$, define

```math
M_k(S)=\min_{p\in\mathbb C[z],\ \deg p\le k,\ p(0)=1}\max_{z\in S}|p(z)|.
```

Is it true, simultaneously for every such $`L`$ and $`1\le k\le n-2`$, that

```math
M_k(L)\le\frac4\pi\max_{S\subseteq L,\ |S|=k+1}M_k(S)?
```

The constant is required to be independent of dimension, degree, and the locations of the points.

For a normal matrix with spectrum $`L`$, $`M_k(L)`$ is the largest relative residual norm attainable at GMRES step $`k`$, over unit initial residuals. The smaller-set quantities have explicit formulas through Lagrange interpolation. The question therefore asks for a sharp, dimension-independent certificate of worst-case convergence using small subsets of the spectrum. It is distinct from equality of ideal and worst-case GMRES for a nonnormal Jordan block (IE-02).

## References

 J. Liesen and P. Tichý, *The worst-case GMRES for normal matrices*, BIT 44 (2004), 79–98, conjecture (3.16), pp. 91–92, and Appendix ([author copy](https://page.math.tu-berlin.de/~liesen/Publicat/LieTic04.pdf)). Their *A min-max problem on roots of unity*, TU Berlin Preprint 28-2003, conclusion (9.1), proves selected roots-of-unity cases and sharpness of $`4/\pi`$ ([university record](https://doi.org/10.14279/depositonce-14263)). Their survey *Convergence analysis of Krylov subspace methods*, GAMM-Mitteilungen 27 (2004), discussion after (11), restates the conjecture ([author copy](https://page.math.tu-berlin.de/~liesen/Publicat/LiTiGAMM.pdf)).

## Status check — 2026-09-08

 Searched the original title with “conjecture”, “4/pi”, “4/π”, “proof”, “counterexample”, and 2025–2026; checked the authors' current publication lists. The later Jordan-block papers concern a different conjecture. No resolution or recent explicit reaffirmation of this particular bound was located; its open-status evidence is historical and bounded.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

## Audit update — 2026-09-10

The [primary paper](https://page.math.tu-berlin.de/~liesen/Publicat/LieTic04.pdf), §3.2.1, proves the stronger subset equality for every real spectrum, a substantive subclass of the displayed target. Its complex-spectrum conjecture remains in §3.2.2. Searches for the Liesen–Tichý conjecture and later sharp normal-GMRES subset bounds found no general resolution; the current status records the real-spectrum partial result without asserting exhaustive literature coverage.
