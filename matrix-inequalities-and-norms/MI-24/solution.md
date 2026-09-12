---
title: "MI-24: the Schatten norm complement follows by convexity"
author: "George Stepaniants"
affiliation: "Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA"
date: "11 September 2026"
document-kind: "Verified resolution"
review-footer: "Independent Codex-agent review; not external human peer review or formal certification."
---

\pagestyle{plain}

The full Schatten norm inequality in MI-24 follows from the published Heron norm inequality of Dinh, Dumitru, and Franco, a positive matrix comparison already used by Ghabries, Abbas, Mourad, and Assi, and the triangle inequality. The last step is a general convexity observation: if one endpoint of a segment has norm at most the midpoint's norm, then the other endpoint has norm at least the midpoint's norm.

**Verification status: independent-agent PASS.** Developed with substantial ChatGPT/Codex assistance. A separate agent checked the complete argument and its primary-source application. [Detailed independent review](../../references/stepaniants-mi24-2026-09-11/verification/reviews/MI-24-review.md). This is independent automated review, not external human peer review or formal verification.

## The full statement

Let $A,B\in\mathbb C^{n\times n}$ be positive definite, where $n\ge1$, and define

$$
\begin{aligned}
G&=A^{1/2}(A^{-1/2}BA^{-1/2})^{1/2}A^{1/2},\\
L&=A^{1/2}(B^{1/2}A^{-1}B^{1/2})^{1/2}A^{1/2}.
\end{aligned}
$$

All square roots are the positive definite square roots. For $1\le p<\infty$, write $\|M\|_p=(\operatorname{tr}|M|^p)^{1/p}$, where $|M|=(M^*M)^{1/2}$; $\|M\|_\infty$ is the largest singular value.

### Theorem 1

For every such pair and every $1\le p\le\infty$,

$$
\boxed{\|A+B+G+L\|_p\le\|A+B+2L\|_p.}
$$

This resolves the complete target of [MI-24](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-24/README.md), equivalently [Ghabries--Abbas--Mourad--Assi, Conjecture 4.1](https://arxiv.org/html/2105.13356v1#S4), including the previously unproved exponents. Neither commutativity nor symmetry of $L(A,B)$ in its arguments is assumed.

## The two comparisons

Put $H=A+B$ and $K=A^{1/2}B^{1/2}+B^{1/2}A^{1/2}$. The published Heron norm inequality of [Dinh--Dumitru--Franco, Theorem 4](https://trunghoamath.wordpress.com/wp-content/uploads/2017/06/p_t_q_t-4-2.pdf), p. 2 of the author manuscript, gives

$$
\|H+2G\|_p\le\|H+K\|_p \qquad(1\le p<\infty). \tag{1}
$$

The same inequality at $p=\infty$ follows by letting $p\to\infty$ in finite dimension. This is the only non-elementary external theorem needed below; it is also recalled in equation (22) and its following paragraph in [Ghabries--Abbas--Mourad--Assi](https://arxiv.org/html/2105.13356v1#S4).

The second comparison is

$$
K\preceq G+L. \tag{2}
$$

For completeness, it has the following direct proof. Set $R=A^{-1/2}B^{1/2}$ and take its polar decomposition $R=U|R|$, where $U$ is unitary. Since $|R^*|=U|R|U^*$,

$$
|R^*|+|R|-R-R^*=(U-I)|R|(U^*-I)\succeq0.
$$

Congruence by $A^{1/2}$ gives (2), because

$$
\begin{aligned}
A^{1/2}|R^*|A^{1/2}&=G,&
A^{1/2}|R|A^{1/2}&=L,\\
A^{1/2}(R+R^*)A^{1/2}&=K.
\end{aligned}
$$

Moreover, $H+K=(A^{1/2}+B^{1/2})^2\succeq0$. Hence (2) implies

$$
0\preceq H+K\preceq H+G+L.
$$

The min--max principle orders every eigenvalue of these positive semidefinite matrices, so

$$
\|H+K\|_p\le\|H+G+L\|_p \qquad(1\le p\le\infty). \tag{3}
$$

This also reproduces the particular comparison in Ghabries--Abbas--Mourad--Assi, Corollary 4.1, without requiring their block-matrix proof as an additional premise.

## The convexity step

**Proof of Theorem 1.** Fix any $p\in[1,\infty]$ and set

$$
X=H+2G,\qquad Y=H+G+L,\qquad Z=H+2L.
$$

Equations (1) and (3) give $\|X\|_p\le\|Y\|_p$. Also $X+Z=2Y$. The triangle inequality therefore gives

$$
2\|Y\|_p=\|X+Z\|_p
\le\|X\|_p+\|Z\|_p
\le\|Y\|_p+\|Z\|_p.
$$

Subtracting $\|Y\|_p$ proves $\|Y\|_p\le\|Z\|_p$, as claimed. $\square$

The proof covers all parameters and dimensions in the canonical statement. Its contribution is the convexity deduction connecting the two existing comparisons; no new proof of the published Heron inequality or historical priority certification is claimed.

## References

1. **Dinh--Dumitru--Franco (2017).** T. H. Dinh, R. Dumitru, and J. A. Franco. *On a conjecture of Bhatia, Lim and Yamazaki*. Linear Algebra and its Applications **532** (2017), 140--145. Theorem 4, equation (4), p. 2 of the [author manuscript](https://trunghoamath.wordpress.com/wp-content/uploads/2017/06/p_t_q_t-4-2.pdf). [DOI: 10.1016/j.laa.2017.06.040](https://doi.org/10.1016/j.laa.2017.06.040).

2. **Ghabries--Abbas--Mourad--Assi (2021/2022).** M. M. Ghabries, H. Abbas, B. Mourad, and A. Assi. *New log-majorization results concerning eigenvalues and singular values and a complement of a norm inequality*. Section 4: equation (22), Corollary 4.1, Theorem 4.2 and Conjecture 4.1, pp. 11--13 of [arXiv:2105.13356v1](https://arxiv.org/abs/2105.13356v1). [Journal DOI: 10.1080/03081087.2022.2059050](https://doi.org/10.1080/03081087.2022.2059050).

3. **MI-24.** ajt60gaibb/OpenProblemsInNLA. *Schatten norm complement involving Lin's positive definite quantity*. [Canonical problem statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-24/README.md). The original mathematical target and permanent identifier are retained.
