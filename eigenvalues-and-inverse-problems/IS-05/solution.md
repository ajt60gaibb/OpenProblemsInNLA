---
title: "Parity obstructions for the conditioning of sign matrices"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
document-kind: "PARTIAL RESULT"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked partial result; the exact exponent remains open.  
**Target:** [IS-05, original catalog snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/IS-05/README.md).  
**Reviewed:** 11 September 2026.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete argument against the exact target; its [detailed review](../../references/colbrook-additional-2026-09-11/verification/reviews/IS-05-review.md) records **PASS** for the partial bound only. The mathematical sections below are unchanged from the reviewed draft. This is independent agent verification, not external human peer review or a formal proof certificate. The [submission record](../../references/colbrook-additional-2026-09-11/README.md) preserves the original manuscript and verification history.

# Target and result

The repository defines
$$
 h(n)=\min_{A\in\{-1,1\}^{n\times n}}\kappa_2(A),
$$
where singular matrices have infinite condition number, and asks for the exact value
$$
 \alpha_*=\sup\{\alpha\ge0:\exists C>0\ \forall n\ge1,
            \ h(n)-1\le Cn^{-\alpha}\}.
 \tag{1}
$$
Its checked formulation records $17/92\le\alpha_*\le1$.[^statement] This note improves the upper bound in that displayed interval, without resolving the exact-value question.

**Theorem 1 (odd-order obstruction).** If $n$ is odd, every nonsingular sign matrix $A\in\{-1,1\}^{n\times n}$ satisfies
$$
 \kappa_2(A)\ge
 \sqrt{1+\frac{n-1}{n^2}}+\frac{\sqrt{n-1}}{n}.
 \tag{2}
$$
Consequently,
$$
 h(n)-1\ge\frac{\sqrt{n-1}}n\quad(n\text{ odd}),
 \qquad \boxed{\alpha_*\le\frac12}.
 \tag{3}
$$

# A variance bound in terms of the condition number

Let $G=A^TA$, let $m,M$ be its smallest and largest eigenvalues, and put $t=M/m=\kappa_2(A)^2$. Since every diagonal entry of $G$ equals $n$, its eigenvalues $\lambda_1,\ldots,\lambda_n$ have mean $n$. Define their variance
$$
 v=\frac1n\sum_{i=1}^n(\lambda_i-n)^2
   =\frac1n\operatorname{tr}(G-nI)^2.
 \tag{4}
$$
Summing the nonnegative quantities $(M-\lambda_i)(\lambda_i-m)$ yields
$$
 v\le(M-n)(n-m)=(tm-n)(n-m).
$$
As a quadratic function of $m$, the last expression is at most its unrestricted maximum,
$$
 v\le\frac{n^2(t-1)^2}{4t}.
 \tag{5}
$$
Writing $\kappa=\kappa_2(A)\ge1$ and taking square roots gives
$$
 \kappa-\kappa^{-1}\ge\frac{2\sqrt v}{n},
 \qquad
 \kappa\ge\sqrt{1+\frac v{n^2}}+\frac{\sqrt v}{n}.
 \tag{6}
$$
This derivation also covers $t=1$; then (5) forces $v=0$.

# Parity supplies the necessary variance

For odd $n$, the inner product of two sign vectors of length $n$ is an odd integer, so every off-diagonal entry $g_{ij}$ of $G$ has $g_{ij}^2\ge1$. Therefore
$$
 v=\frac1n\sum_{i\ne j}g_{ij}^2\ge n-1.
 \tag{7}
$$
Substituting (7) into (6) proves (2), and hence the first part of (3).

Suppose some $\alpha>1/2$ were admissible in (1). For every odd $n$,
$$
 C\ge n^\alpha(h(n)-1)
   \ge n^{\alpha-1}\sqrt{n-1}.
$$
The right-hand side diverges along the odd integers, a contradiction. This proves the upper bound on $\alpha_*$. Singular matrices cause no exception: their infinite condition numbers satisfy the lower bounds automatically and do not improve the minimum.

# An additional bound for orders equal to two modulo four

**Theorem 2.** If $n\equiv2\pmod4$, every nonsingular sign matrix of order $n$ satisfies
$$
 \kappa_2(A)\ge
 \sqrt{1+\frac{2(n-2)}{n^2}}+\frac{\sqrt{2(n-2)}}n.
 \tag{8}
$$

**Proof.** Form a graph whose vertices are the columns of $A$, with an edge for each pair of orthogonal columns. This graph is triangle-free. Indeed, if three sign columns were pairwise orthogonal, multiply their rows by signs to make the first column all ones. The second has $n/2$ plus entries and $n/2$ minus entries. Orthogonality of the third to the first two forces its sum on each of these two halves to be zero. Each half must consequently have even size, implying $4\mid n$, a contradiction.

A triangle-free graph on $n$ vertices has at most $n^2/4$ edges. To see this directly, for every edge $uv$ its endpoint degrees satisfy $d_u+d_v\le n$. Summing over all $e$ edges gives $\sum_vd_v^2\le ne$, whereas Cauchy--Schwarz gives $\sum_vd_v^2\ge(2e)^2/n$. Thus $e\le n^2/4$ (including $e=0$).

At least
$$
 \frac{n(n-1)}2-\frac{n^2}4=\frac{n(n-2)}4
$$
unordered column pairs therefore have nonzero inner products. These inner products are even integers and have square at least four. Counting both orders in (4) gives
$$
 v\ge\frac2n\,4\,\frac{n(n-2)}4=2(n-2).
$$
Equation (6) now proves (8).

# What remains open

Combining Theorem 1 with the lower bound quoted by the repository gives the proposed updated interval
$$
 \frac{17}{92}\le\alpha_*\le\frac12.
$$
No construction establishing the matching exponent $1/2$ is supplied here. Theorems 1 and 2 are therefore partial progress, not a solution to the exact-value target. The repository submission records **Partially resolved**, with the exact exponent still open.

The verification script checks the finite-dimensional inequalities on small sign matrices. The all-orders proof is (4)--(8), not the finite tests. Whether these elementary bounds have appeared elsewhere remains to be checked before any novelty claim.

# Sources

[^statement]: *Open Problems in Numerical Linear Algebra*, IS-05, “The optimal decay exponent for the conditioning of sign matrices,” checked 11 September 2026; [canonical entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IS-05/README.md).

1. *Open Problems in Numerical Linear Algebra*, IS-05, [canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IS-05/README.md), checked 11 September 2026.
2. B. Alexeev, J. Jasper, and D. G. Mixon, *Asymptotically optimal approximate Hadamard matrices*, [arXiv:2511.14653v1](https://arxiv.org/html/2511.14653v1), §6, Problem 11; the primary reference identified by the repository for the exponent question and its quoted bounds.

3. The later [arXiv version 2](https://arxiv.org/html/2511.14653v2), dated 18 August 2026, retains the construction exponent below $17/92$ and the earlier obstruction in §5, Problem 11. The independent review checked this current source; the new upper-bound proof above is unchanged.
