# PF-05 — Infinitesimal rigidity detects unique size-two factors in the presence of zeros

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Rating rationale:** Challenging because zeros change the feasible infinitesimal motions and defeat the positive-entry argument; specialist importance is a precise uniqueness test for size-two PSD factors.  
**Status:** Partially resolved  
**Last checked:** 2026-09-10  

## Context and notation

Write $\mathbb S_+^k$ for the cone of real symmetric positive semidefinite $k\times k$ matrices. For an entrywise nonnegative matrix $M\in\mathbb R_+^{p\times q}$, its **real positive semidefinite rank** is

$$
\operatorname{rank}_{\rm psd}(M)
=\min\{k\ge1:\ \exists A_1,\ldots,A_p,B_1,\ldots,B_q\in\mathbb S_+^k,\quad
M_{ij}=\operatorname{tr}(A_iB_j)\ \text{for all }i,j\}.
$$

This definition concerns a family of matrix factors indexed by the rows and columns of $M$.

## Problem statement

Let $M\in\mathbb R_+^{p\times q}$ satisfy $\operatorname{rank}(M)=3$ and
$\operatorname{rank}_{\rm psd}(M)=2$, and fix any size-two factorization
$M_{ij}=\operatorname{tr}(A_iB_j)$. Zero entries of $M$ are allowed.

Call a collection of real symmetric matrices $(E_i,F_j)$ a feasible linear
direction if

$$
\operatorname{tr}(E_iB_j)+\operatorname{tr}(A_iF_j)=0\quad\text{for every }i,j
$$

and some $h>0$ satisfies $A_i+tE_i\succeq0$, $B_j+tF_j\succeq0$ for
all $i,j$ and $t\in[0,h)$. The trace constraint is imposed only to first
order; the perturbed factors need not represent $M$ at positive $t$.

### Question

Are the following conditions equivalent for every such factorization?

1. Every feasible linear direction has the form $E_i=dA_i$, $F_j=-dB_j$
   for one real scalar $d$ common to all factors.
2. Every other size-two factorization $(\widetilde A_i,\widetilde B_j)$ of
   $M$ satisfies $\widetilde A_i=S^\mathsf T A_iS$ and
   $\widetilde B_j=S^{-1}B_jS^{-\mathsf T}$ for one $S\in GL(2,\mathbb R)$.

This asks whether an infinitesimal test certifies uniqueness of the optimal
matrix factors up to changes of basis. Condition 1 is exactly the source's
2-infinitesimal rigidity: for size two, the relevant second-degree Taylor
polynomials are the complete principal minors, and Theorem 2.2 identifies the
trivial directions as the common scalings above.

## Reference and status

K. Dawson, S. Hoşten, K. Kubjas, and L. Metsälampi,
[*Uniqueness of size-2 positive semidefinite matrix factorizations*, v2](https://arxiv.org/html/2410.18891v2),
31 August 2026, Definition 1, Remark 1, Theorem 2.2, and the conjecture immediately
after Theorem 5.2. Theorem 5.2 proves the assertion when every entry of $M$ is
strictly positive. Lemma 19 identifies local and global rigidity in the stated
rank class, so omitting the equivalent local condition does not weaken the
source's remaining conjecture. Searches for the title, PSD rigidity with zeros,
and later work found no resolution beyond this latest version.

## Status check — 2026-09-10

Rechecked [Dawson–Hoşten–Kubjas–Metsälampi v2, Theorem 2.2, Theorem 5.2 and its following conjecture](https://arxiv.org/html/2410.18891v2), and searched for later rigidity results with zero entries. The August 31, 2026 revision proves equivalence for strictly positive M and conjectures its extension to matrices with zeros. Those positive matrices are a proved part of the displayed target. No resolution of the zero-entry remainder was located.
