# AC-09 — Deterministic polynomial-time commutative Edmonds problem

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Rating rationale:** Extreme because deterministic symbolic nonsingularity is a central derandomization barrier; broad importance links matrix-space rank, polynomial identity testing and complexity theory.  
**Provenance:** source-stated problem, with rational input and bit complexity made explicit.  
**Last checked:** 2026-09-10  

**Status:** Partially resolved  

The input consists of positive integers $n,s$ and matrices $A_1,\ldots,A_s\in\mathbb Q^{n\times n}$, with rational entries represented by signed binary numerators and positive binary denominators. Does there exist a deterministic algorithm, running in a number of bit operations bounded by a polynomial in the total binary input length, that decides whether
$$
\det\!\left(\sum_{i=1}^s x_iA_i\right)
$$
is the zero polynomial in the commuting indeterminates $x_1,\ldots,x_s$ over $\mathbb Q$?

Equivalently, decide whether the rational linear space
$$
\left\{\sum_{i=1}^s c_iA_i:\ c_1,\ldots,c_s\in\mathbb Q\right\}
$$
contains a nonsingular matrix. No prescribed matrix structure is assumed.

This is exact rank and nonsingularity testing for a parametrized matrix space. Random evaluation gives a randomized route; the problem asks whether randomness can be eliminated while retaining polynomial running time.

## References

1. C. Chindris and D. Kline, *Edmonds' problem and the membership problem for orbit semigroups of quiver representations*, arXiv:2008.13648 (2020), introduction: the general deterministic nonsingularity problem and the special classes treated in the paper. [Paper](https://arxiv.org/html/2008.13648v1).
2. G. Ivanyos, M. Karpinski, Y. Qiao, and M. Santha, *Generalized Wong sequences and their applications to Edmonds' problems*, arXiv:1307.6429v2 (2014), abstract and introduction: symbolic determinant identity testing, including the rational field and algorithms for restricted matrix spaces. [Paper](https://arxiv.org/abs/1307.6429).
3. A. Chatterjee, S. Ghosh, R. Gurjar, R. Raj, and T. Thierauf, *Bipartite Matching is in NC*, ECCC TR26-100, revision 2 (2026), Section 1.1, “Non-commutative rank”: explicitly distinguishes the still-open deterministic commutative rank problem. [Report and version history](https://eccc.weizmann.ac.il/report/2026/100/).

## Status check — 2026-09-10

Rechecked [Chatterjee et al., ECCC TR26-100, §1.1](https://eccc.weizmann.ac.il/report/2026/100/download/), and searched for later commutative Edmonds algorithms. The July 2026 revision explicitly states that no deterministic polynomial-time algorithm is known generally. [Ivanyos et al.](https://arxiv.org/abs/1307.6429) gives algorithms for restricted matrix spaces, substantive solved subclasses. Deterministic noncommutative-rank algorithms and bipartite matching do not settle unrestricted commuting symbolic determinants. No full resolution was located.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
