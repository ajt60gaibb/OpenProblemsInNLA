---
title: "KE-04: Strict interval occupancy across block Lanczos iterations"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked resolution (Codex-agent review).  
**Outcome:** Affirmative resolution.  
**Prepared:** 11 September 2026.  
**Target:** [Repository entry KE-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/KE-04/README.md), snapshot `b412319`.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete proof against the exact repository target on 11 September 2026; its [detailed review](../../references/colbrook-2026-09-11/verification/reviews/KE-04-review.md) records **PASS**. The theorem and proof text below are unchanged from the reviewed submission. This verification is an independent agent review, not external human peer review or a formal proof certificate.

## Theorem KE-04: proposed strict interval occupancy

Let $A\in\mathbb R^{n\times n}$ be symmetric and let $V\in\mathbb R^{n\times p}$ have full column rank. Define
$$
\mathcal K_\ell=\operatorname{range}[V,AV,\ldots,A^{\ell-1}V].
$$
Assume $\dim\mathcal K_s=sp$ and therefore full block dimension at all preceding iterations. Let $P_\ell$ be the orthogonal projector onto $\mathcal K_\ell$, and let $H_\ell=P_\ell A|_{\mathcal K_\ell}$. Write its eigenvalues, with multiplicity, as
$$
\theta_1^{(\ell)}\le\cdots\le\theta_{\ell p}^{(\ell)}.
$$
These are the Ritz values and are independent of the chosen orthonormal basis.

**Claim.** For every $1\le k<j\le s$ and every $1\le i\le(k-1)p$, the open interval
$$
(\theta_i^{(k)},\theta_{i+p}^{(k)})
$$
contains an eigenvalue of $H_j$.

### 1. Assume a gap at the later iteration

There are no admissible indices when $k=1$, so suppose $k\ge2$. Put
$$
a=\theta_i^{(k)},\qquad b=\theta_{i+p}^{(k)},\qquad
q(t)=(t-a)(t-b).
$$
Suppose that $H_j$ has no eigenvalue in $(a,b)$. Since $a\le b$,
$$
q(H_j)\succeq0.
$$
Let $E\subseteq\mathcal K_k$ be the span of an orthonormal set of eigenvectors of $H_k$ corresponding to indices $i,\ldots,i+p$. Then
$$
\dim E=p+1,\qquad \langle x,q(H_k)x\rangle\le0\quad(x\in E).
$$
The codimension of $\mathcal K_{k-1}$ in $\mathcal K_k$ is $p$, so $E\cap\mathcal K_{k-1}$ contains a nonzero vector $x$.

### 2. The quadratic forms agree on that vector

Since $x\in\mathcal K_{k-1}$, we have $Ax\in\mathcal K_k$ and
$$
H_kx=H_jx=Ax.
$$
Self-adjointness of the compressions gives
$$
\begin{aligned}
\langle x,q(H_j)x\rangle
&=\|Ax\|^2-(a+b)\langle x,Ax\rangle+ab\|x\|^2\\
&=\langle x,q(H_k)x\rangle\le0.
\end{aligned}
$$
Combined with $q(H_j)\succeq0$, this implies $q(H_j)x=0$.

Moreover $A^2x\in\mathcal K_{k+1}\subseteq\mathcal K_j$, so $H_j^2x=A^2x$. Hence
$$
q(A)x=0.
$$

### 3. Full block rank excludes this annihilation

Write
$$
x=\sum_{\ell=0}^{k-2}A^\ell Vc_\ell.
$$
Let $r$ be the largest index with $c_r\ne0$; such an index exists because $x\ne0$. The polynomial $q$ is monic of degree two. Therefore the coefficient of $A^{r+2}V$ in the resulting block-power expansion of $q(A)x$ is exactly $c_r\ne0$.

Since $k+1\le j\le s$, the block Krylov matrix
$$
[V,AV,\ldots,A^kV]
$$
has full column rank. As $r+2\le k$, the nonzero coefficient just found implies $q(A)x\ne0$, a contradiction.

This establishes the claim for all admissible indices and iterations. If $a=b$, the same argument applies with $q(t)=(t-a)^2$ and rules out that case; thus the proof does not presuppose strictly separated endpoints or simple Ritz values. $\square$

## Scope and review notes

The argument uses real symmetric A, a full-column-rank starting block, exact arithmetic, and full block dimension through iteration j. It includes eigenvalue multiplicities and the possibility of coincident proposed interval endpoints, which it rules out in the relevant range. It does not assert a finite-precision analogue.

The independent review checked the equality of the two quadratic forms on a vector in $\mathcal K_{k-1}$, followed by conversion to a degree-two annihilating polynomial. Full rank is required through $\mathcal K_{k+1}$, which is guaranteed by $k+1\le j\le s$.

The packaging pass checked the repository statement and contribution rules on 11 September 2026. It did not conduct a new exhaustive literature search or establish novelty.

## Source references

Alex Townsend, *Open Problems in Numerical Linear Algebra* (2026), [entry KE-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/KE-04/README.md), repository snapshot `b412319`, accessed 11 September 2026.

D. Šimonová and P. Tichý, *On finite precision block Lanczos computations*, [arXiv manuscript, version 1](https://arxiv.org/abs/2507.16484v1), 22 July 2025, §2.1, unnumbered conjecture. The catalog identifies this as the source of its exact-arithmetic interval statement.
