# Primary sources and audit notes

Sources were accessed on September 12, 2026. The bibliography in the manuscript gives the corresponding citations at the points of use. Source PDFs are not redistributed.

## Problem statement

**OpenProblemsInNLA, RA-17 — Minimum linear measurements for uniform recovery of real low-rank matrices.** Catalogue audit dated September 10, 2026.

<https://raw.githubusercontent.com/ajt60gaibb/OpenProblemsInNLA/main/randomized-and-low-rank-approximation/RA-17/README.md>

The target is an exact count for all allowed dimensions and ranks, with unrestricted real matrices and uniform injectivity. The archive's interval calculator is not a substitute for that target.

## Original measurement construction and accompanying data

**Zhiqiang Xu, The minimal measurement number for low-rank matrices recovery**, arXiv:1505.07204v1 (2015), Theorem 3.2 and equation (3.5), page 6. The paper also supplies the determinantal-degree background. Published-version DOI: 10.1016/j.acha.2017.01.005.

<https://arxiv.org/pdf/1505.07204v1>

**Zhiqiang Xu, accompanying Maple verification webpage.**

<https://lsec.cc.ac.cn/~xuzq/rank1.htm>

The two data sources differ as follows, with one-based indexing in the displayed source matrices:

| Entry | Printed paper | Website |
|---|---:|---:|
| `A_4(2,4)` | 3 | 4 |
| `A_8(4,3)` | 3 | 2 |

The archive uses simultaneous transposes of the displayed matrices with row-major vectorization. Consequently these positions become `W[4,14]` and `W[8,12]`, again with one-based indexing. Both complete variants are independently certified; no claim that either discrepancy invalidates the corresponding construction is made.

The Macaulay-matrix/eigenvalue certificate in this archive is regenerated from the matrices. Its validity does not depend on treating a truncated row reduction as a complete Gröbner basis. Its separate infinite-chart check rules out every nonzero point with the homogenizing coordinate zero, even over the complex numbers.

## Current survey

**Zhiqiang Xu, Signal Recovery on Algebraic Varieties Using Linear Samples**, arXiv:2506.17572v2, Section 5, Theorem 5.5 and Remark 5.6. Published in *Acta Mathematica Sinica* 42 (2026), 740–754; DOI 10.1007/s10114-026-5299-y.

<https://arxiv.org/html/2506.17572v2>

Used to confirm the real-versus-complex distinction and the stated exact dimension families. No full real classification is inferred from this source.

## Grassmannian cohomology

**Jeffrey D. Carlson, Grassmannians and the equivariant cohomology of isotropy actions**, arXiv:1611.01175v2 (2023), Corollary 2.3, pages 10–11.

<https://arxiv.org/pdf/1611.01175v2>

**Chen He, Localization of equivariant cohomology rings of real and oriented Grassmannians**, arXiv:1609.06243, Corollary 5.26, page 19 of the accessed preprint.

<https://arxiv.org/pdf/1609.06243>

These sources support the rational **unoriented** Grassmannian presentations used in Section 4. The evaluation-bundle application and Euler-square arguments are given in full in the manuscript rather than attributed to these sources. In the odd-dimensional ambient case, the proof tracks the orientation local system explicitly.

**Ákos K. Matszangosz and Matthias Wendt, The mod 2 cohomology rings of oriented Grassmannians via Koszul complexes**, *Mathematische Zeitschrift* 308, article 2 (2024), Section 3.1.

<https://doi.org/10.1007/s00209-024-03556-y>

Despite the article title, the specific presentation invoked here is the recalled **unoriented** Grassmannian ring, not a replacement of the oriented ring by a simpler quotient.

## Corank-one obstruction

**Andrea Causin, On the dimension of some real, bounded rank, matrix spaces**, arXiv:0911.1810v1 (2009), Proposition 2.2 and Theorem 3.5.

<https://arxiv.org/pdf/0911.1810v1>

The manuscript uses the upper bound `kappa <= 2*nu_2(d)+2` and gives the cofactor-map argument. Exactness is asserted only where an explicit construction matches that bound.

**Scope caution.** The wording “8 divides n” in Proposition 3.6 of this arXiv version is broader than the equality that follows from its preceding displayed Hurwitz–Radon bounds alone. For example, at `d=16` those bounds are 9 and 10. This archive does not rely on that broader statement and does not claim to have disproved it. The intervals reported in the archive are the bounds its own arguments establish, not a complete review of all optimal bounds in the literature.

## Historical construction reference

**Elmer G. Rees, Linear spaces of real matrices of large rank**, *Proceedings of the Royal Society of Edinburgh Section A* 126 (1996), 147–151; DOI 10.1017/S030821050003064X.

<https://doi.org/10.1017/S030821050003064X>

Cited as background for large-minimum-rank spaces. The anti-diagonal construction and all coefficient identities needed for the supplied constructions are proved directly in the manuscript.

## Attribution and verification boundary

No priority claim is made for the arguments, exact cases, or bounds. “Certified” refers to the executed rational algebraic computations and the precise certificates supplied; it does not imply that the characteristic-class proofs are proof-assistant formalizations or that the manuscript has undergone external peer review. The complete all-dimension target remains unestablished in this archive.
