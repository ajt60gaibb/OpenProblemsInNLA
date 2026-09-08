# AC-09 — Deterministic polynomial-time commutative Edmonds problem

**Difficulty:** extreme  
**Importance:** broadly interesting  
**Provenance:** source-stated problem, with rational input and bit complexity made explicit.  
**Last checked:** 2026-09-08

**Status:** no general deterministic polynomial-time algorithm found in screening on 2026-09-08.  

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

## Status check — 2026-09-08

searched “commutative Edmonds 2026” and “Edmonds rational deterministic polynomial rank matrix space”; checked the current arXiv records and ECCC revision 2 dated 2026-07-15. The 2026 report still states that no deterministic polynomial-time algorithm is known for commutative symbolic matrix rank. Deterministic algorithms for noncommutative rank and for rank-one-spanned or triangularizable matrix spaces do not settle this unrestricted commuting-variable problem. No full resolution or relevant source withdrawal was found.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
