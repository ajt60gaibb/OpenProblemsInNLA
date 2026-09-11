# SP-15 — Finitely many unitary classes with prescribed shifted singular values

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Inverse determination from complete pseudospectral data  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** Generic finiteness follows from invariant theory, but the exceptional fibers resist that argument; the question measures how much complete pseudospectral data can identify a nonnormal matrix.

## Context and notation

For a complex $N\times N$ matrix $M$, write
$s_1(M)\geq\cdots\geq s_N(M)$ for its singular values. Say $A\sim_{\rm sip} B$
if

$$
s_j(A-zI)=s_j(B-zI)
\qquad(z\in\mathbb C,\ 1\leq j\leq N).
$$

This is equality of *super-identical pseudospectral* data: it includes every
singular value of every scalar shift.

## Problem statement

Is it true that for every $N\geq1$ there is an integer $M_N\geq1$ such that
every family $A_1,\ldots,A_{M_N+1}\in\mathbb C^{N\times N}$ with
$A_i\sim_{\rm sip}A_j$ for all $i,j$ contains a pair satisfying

$$
A_j=U^*A_iU\quad\text{for some }i<j\text{ and }U^*U=I?
$$

Equivalently, is every such data fiber a union of at most $M_N$ unitary similarity
classes, with a bound depending only on $N$?

## References

- Maxime Fortier Bourque and Thomas Ransford, [*Super-identical pseudospectra*](https://doi.org/10.1112/jlms/jdn085), *Journal of the London Mathematical Society* **79**(2), 511–528 (2009), **Theorem 1.4 and §6.2**. The theorem removes a closed measure-zero exceptional set; the question asks to remove this exception. [Author manuscript](https://analyse.mat.ulaval.ca/abstracts/2008-03.pdf).
- Thomas Ransford, [*Pseudospectra and matrix behaviour*](https://analyse.mat.ulaval.ca/abstracts/2010-01.pdf), **Theorem 5.4 and the following discussion, pp. 10–11**. This restates the finiteness theorem and explicitly leaves the empty-exceptional-set case open. It explains why replacing algebraicity with integrality fails to prove it.
- G. Armentia, J. M. Gracia and F. E. Velasco, [*Identical pseudospectra of any geometric multiplicity*](https://doi.org/10.1016/j.laa.2011.01.014), *Linear Algebra and its Applications* **436**(6), 1683–1688 (2012). Their similarity theorem for super-identical pseudospectra gives ordinary similarity, which allows nonunitary changes of basis and does not answer the displayed question.
- T. Ransford and N. Walsh, [*A four-mean theorem and its application to pseudospectra*, arXiv:2109.14472v2](https://arxiv.org/pdf/2109.14472v2), 9 July 2022, Theorems 1.3–1.4. Polynomial-norm comparisons and similarity-conditioning bounds do not establish finiteness of the unitary classes; the related norm question is retained in [MF-24](../../matrix-functions-and-stability/MF-24/README.md).

The original low-dimensional results give $M_2=1$ and $M_3=2$; $M_1=1$ is
immediate. The unresolved question concerns exceptional data fibers in higher
dimensions, rather than generic matrices.

## Scope and status check

The quantifiers above are an explicit restatement of the source question about
the exceptional set, with $M_N$ counting classes instead of the source's
pigeonhole family size. The source is older: current openness rests on bounded
later-literature searches, not a recent explicit reaffirmation. Searches through
2026-09-11 for super-identical pseudospectra, finite unitary classes, the
exceptional set and related similarity results found no resolution. The 2012
ordinary-similarity theorem and the cited 2022 norm estimates were checked for
scope. They do not remove the exceptional set.
