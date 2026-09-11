---
title: "KE-03: Locating a near-largest eigenvalue in the exact-query model"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked resolution (Codex-agent review).  
**Outcome:** Affirmative resolution in the displayed exact-query model.  
**Prepared:** 11 September 2026.  
**Target:** [Repository entry KE-03](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/KE-03/README.md), snapshot `b412319`.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete proof against the exact repository target on 11 September 2026; its [detailed review](../../references/colbrook-2026-09-11/verification/reviews/KE-03-review.md) records **PASS**. The theorem and proof text below are unchanged from the reviewed submission. This verification is an independent agent review, not external human peer review or a formal proof certificate.

## Theorem KE-03: proposed exact-query algorithm

Suppose $A\in\mathbb C^{n\times n}$ is diagonalizable,
$$
A=V\Lambda V^{-1},\qquad \|V\|_2\|V^{-1}\|_2\le K,
\qquad \rho=\rho(A)>0,
$$
where $K\ge1$ is supplied but $V$ and $\Lambda$ are not. Only exact queries $v\mapsto Av$ are permitted.

**Claim.** For every $0<\varepsilon<1/2$, a randomized algorithm using
$$
O\!\left(\varepsilon^{-2}[1+\log(nK)]\right)
$$
queries returns $z\in\mathbb C$ with probability at least $0.997$ such that some $\mu\in\sigma(A)$ satisfies
$$
|\mu|\ge(1-\varepsilon)\rho,\qquad |z-\mu|\le\varepsilon\rho.
$$
All intervening work is finite exact arithmetic. Its bit complexity and floating-point stability are not bounded here.

### 1. A simultaneous polynomial estimate

Choose an integer $N\ge1000n$ such that $N+1$ is a power of two. Sample each coordinate of $b\in\mathbb R^n$ independently and uniformly from
$$
\{0,1/N,\ldots,1\}.
$$
This uses finitely many random bits. Set $F=1000n^2K$.

**Lemma.** With probability at least $0.997$, simultaneously for every complex polynomial $p$,
$$
F^{-1}\max_{\lambda\in\sigma(A)}|p(\lambda)|
\le\|p(A)b\|_2
\le F\max_{\lambda\in\sigma(A)}|p(\lambda)|.
$$

**Proof.** Let $w_i$ be row $i$ of $V^{-1}$. Choose a coordinate $j$ with $|(w_i)_j|\ge\|w_i\|_2/\sqrt n$. Conditional on the other coordinates of $b$, the event
$$
|w_ib|<\frac{\|w_i\|_2}{1000n^2}
$$
restricts the real variable $b_j$ to an interval of length at most $2/(1000n^{3/2})$. This remains true for complex $w_i$: intersection of a disk with a line has diameter at most the disk's diameter. An interval of length $\ell$ contains at most $N\ell+1$ grid points. Thus the event has probability at most
$$
\frac{2}{1000n^{3/2}}+\frac1{N+1}\le\frac3{1000n}.
$$
A union bound gives, with probability at least $0.997$, for every $i$,
$$
|(V^{-1}b)_i|\ge\frac{\|w_i\|_2}{1000n^2}
\ge\frac1{1000n^2\|V\|_2}.
$$
The last inequality follows from $w_iV=e_i^T$. On this event, for every $p$,
$$
\begin{aligned}
\|p(A)b\|_2
&\ge\frac{\|p(\Lambda)V^{-1}b\|_2}{\|V^{-1}\|_2}\\
&\ge\frac{\max_i|p(\lambda_i)|}
 {1000n^2\|V\|_2\|V^{-1}\|_2}
\ge F^{-1}\max_i|p(\lambda_i)|.
\end{aligned}
$$
The deterministic upper bound is
$$
\|p(A)b\|_2\le K\|b\|_2\max_i|p(\lambda_i)|
\le K\sqrt n\max_i|p(\lambda_i)|\le F\max_i|p(\lambda_i)|.
$$
This proves the lemma. Its event depends only on $b$, so it also covers adaptively selected polynomials. $\square$

### 2. Query phase

Put
$$
\eta=\frac{\varepsilon^2}{1024},\qquad
m=\left\lceil\frac{\log F}{\log(1+\eta)}\right\rceil.
$$
Use $m$ queries to compute $b,Ab,\ldots,A^mb$. For any $s\in\mathbb C$, the vector
$$
(A+sI)^mb=\sum_{\ell=0}^m\binom m\ell s^{m-\ell}A^\ell b
$$
can now be computed without further queries.

For analysis, write
$$
q_s=\|(A+sI)^mb\|_2^{1/m},\qquad R_s=\rho(A+sI).
$$
On the event of the lemma,
$$
(1+\eta)^{-1}R_s\le q_s\le(1+\eta)R_s
\quad\hbox{for every }s\in\mathbb C.
$$
Compute a positive multiplicative approximation $r$ to $q_0$ satisfying
$$
(1+\eta)^{-1}q_0\le r\le(1+\eta)q_0.
$$
The finite-arithmetic implementation is given below. On the success event,
$$
(1+\eta)^{-2}\rho\le r\le(1+\eta)^2\rho.
$$

### 3. Selection among shifts

Choose a finite unit-circle net $\{u_\ell\}$ such that every unit complex number is within chordal distance $\varepsilon/8$ of some $u_\ell$. A construction with $O(1/\varepsilon)$ rational points is given below.

Compute all squared norms $\|(A+ru_\ell I)^mb\|_2^2$, using the stored block powers. Choose any maximizing index $\widehat\ell$, and return
$$
z=ru_{\widehat\ell}.
$$
This selection requires no further oracle queries.

### 4. Location guarantee

Choose $\mu_*\in\sigma(A)$ with $|\mu_*|=\rho$. Some net point $u_*$ obeys $|\mu_*/\rho-u_*|\le\varepsilon/8$, so
$$
R_{ru_*}^2\ge|\mu_*+ru_*|^2
\ge(\rho+r)^2-\frac{\rho r\varepsilon^2}{64}.
$$
By the maximizing selection and the bounds on $q_s$,
$$
R_z\ge(1+\eta)^{-2}R_{ru_*}.
$$
Take $\mu\in\sigma(A)$ attaining $R_z=|\mu+z|$, and let $a=(1+\eta)^{-4}$. Since $|\mu|\le\rho$ and $|z|=r$,
$$
\begin{aligned}
|\mu-z|^2
&=2(|\mu|^2+r^2)-|\mu+z|^2\\
&\le(\rho-r)^2+(1-a)(\rho+r)^2
  +a\frac{\rho r\varepsilon^2}{64}.
\end{aligned}
$$
The bounds on $r$ imply $|\rho-r|\le3\eta\rho$ and $r\le2\rho$. Also $1-a\le4\eta$. Consequently
$$
|\mu-z|^2
\le\left(9\eta^2+36\eta+\frac{\varepsilon^2}{32}\right)\rho^2
<\frac{\varepsilon^2\rho^2}{9}.
$$
For the final inequality, divide by $\varepsilon^2$ and use $\varepsilon^2<1/4$:
$$
\frac{9\varepsilon^2}{1024^2}+\frac{36}{1024}+\frac1{32}<\frac19.
$$
Thus $|z-\mu|<\varepsilon\rho/3$, and
$$
|\mu|\ge r-|z-\mu|
\ge(1-2\eta-\varepsilon/3)\rho
\ge(1-\varepsilon)\rho.
$$
Both requested guarantees follow on the same event of probability at least $0.997$.

### 5. Finite exact arithmetic and query count

The displayed logarithms and roots need not be primitive exact operations. Find $m$ by repeated multiplication and comparison until $(1+\eta)^m\ge F$; this gives the same integer as the ceiling formula.

If $\|A^mb\|_2^2=0$, return zero immediately. This event is impossible on the success event because $\rho>0$. Otherwise bracket $q_0$ with positive powers of two, comparing their $2m$-th powers with $\|A^mb\|_2^2$. Starting from such a bracket $[L,U]$, bisect until $U\le(1+\eta)L$. Choosing $r=L$ gives the required multiplicative approximation. Bracketing and bisection terminate for every positive input in finite exact arithmetic.

For an exact unit-circle net, set
$$
u(t)=\frac{1-t^2+2it}{1+t^2},\qquad -1\le t\le1.
$$
Use $u(t)$ and $-u(t)$ on a rational uniform mesh of spacing at most $\varepsilon/8$ including both endpoints. Together the two arcs cover the circle. Since $|u'(t)|\le2$ and a point of the parameter interval is within half a mesh spacing of a mesh point, the required chordal error is at most $\varepsilon/8$. Such a mesh has $O(1/\varepsilon)$ points and uses rational arithmetic. Its size can be found by comparisons, without an exact ceiling primitive.

The shift selection compares squared norms directly; no $m$-th roots are needed. Complex arithmetic and squared norms can be implemented with arithmetic on real and imaginary parts. No multiplication by $A^*$ and no shifted linear-system solve is used.

Finally, $\log F=O(1+\log(nK))$ and $\log(1+\eta)\ge\eta/2$, so
$$
m=O\!\left(\varepsilon^{-2}[1+\log(nK)]\right).
$$
This proves the proposed query-complexity bound. Unrestricted intervening work is essential to the stated scope; no practical numerical implementation is certified. $\square$

## Scope and review notes

The input is any diagonalizable complex A with positive spectral radius and a supplied eigenvector-condition bound K. Only queries v -> Av are used. Intervening work is finite exact arithmetic, with unrestricted cost and precision, as allowed by the displayed target. No A* oracle or shifted-system oracle is used. This is not a floating-point stability, bit-complexity, or total-runtime result.

The independent review checked simultaneous anti-concentration for complex eigenvector coordinates, adaptive use of the same Krylov sequence, shift-selection geometry, and finite-arithmetic termination. The supplied diagnostic code checks only the shift geometry, not an end-to-end stable implementation of the high-degree algorithm.

The packaging pass checked the repository statement and contribution rules on 11 September 2026. It did not conduct a new exhaustive literature search or establish novelty.

## Source references

Alex Townsend, *Open Problems in Numerical Linear Algebra* (2026), [entry KE-03](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/KE-03/README.md), repository snapshot `b412319`, accessed 11 September 2026.

Amsel et al., workshop report, [arXiv:2602.05394v3](https://arxiv.org/abs/2602.05394v3), Problem 3.9. The exact oracle formulation with supplied K is the displayed repository target; the present claim is explicitly limited to that formulation rather than every possible interpretation of the workshop question.
