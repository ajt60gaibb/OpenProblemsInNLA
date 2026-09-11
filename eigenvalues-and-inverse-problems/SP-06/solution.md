---
title: "A real Jordan-curve symbol with a nonreal finite Toeplitz spectrum"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
document-kind: "RESOLUTION"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked negative resolution (Codex-agent review).  
**Target:** [SP-06, original catalog snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/SP-06/README.md).  
**Reviewed:** 11 September 2026.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete argument against the exact target; its [detailed review](../../references/colbrook-additional-2026-09-11/verification/reviews/SP-06-review.md) records **PASS**. The mathematical sections below are unchanged from the reviewed draft. This is independent agent verification, not external human peer review or a formal proof certificate. The [submission record](../../references/colbrook-additional-2026-09-11/README.md) preserves the original manuscript and verification history.

# The target

For a Laurent polynomial $b(z)=\sum_{k=-r}^s b_kz^k$, with $r,s\ge1$ and $b_{-r}b_s\ne0$, the repository asks whether the existence of a Jordan curve $\gamma\subset\mathbb C\setminus\{0\}$ on which $b$ is real implies
$$
 \operatorname{spec}(T_n(b))\subset\mathbb R
 \quad\hbox{for every }n\ge1,
 \qquad T_n(b)=(b_{i-j})_{i,j=1}^n.
$$
This is the finite-section implication retained as conjectural after the correction to the Shapiro--Štampach article.[^statement]

**Theorem 1.** The Laurent polynomial
$$
 b(z)=-64z^{-2}+8z^{-1}-128-8z-63z^2-16z^3-z^4
 \tag{1}
$$
is real on a star-shaped Jordan curve enclosing zero, but
$$
 \operatorname{spec}(T_2(b))=\{-128+8i,-128-8i\}.
 \tag{2}
$$
Consequently, the universal finite-spectrum implication in SP-06 is false.

# Construction of a genuine Jordan curve

Define
$$
 a(z)=8z^{-1}+8z+z^2,
 \qquad F(r,t)=r^2-1+\frac{r^3}{4}\cos t.
 \tag{3}
$$
For every real $t$,
$$
 F(1/2,t)=-\frac34+\frac1{32}\cos t<0,
 \qquad F(2,t)=3+2\cos t\ge1.
$$
For $1/2\le r\le2$,
$$
 \frac{\partial F}{\partial r}
 =2r+\frac34r^2\cos t
 \ge r\left(2-\frac34r\right)\ge\frac r2>0.
 \tag{4}
$$
The intermediate value theorem and strict monotonicity therefore give a unique root $r=\rho(t)\in(1/2,2)$ of $F(r,t)=0$.

The function $\rho$ is continuous. For example, if $t_j\to t$, compactness supplies convergent subsequences of $\rho(t_j)$; any limit satisfies $F(r,t)=0$, so uniqueness forces the limit to equal $\rho(t)$. Uniqueness also gives $2\pi$-periodicity. Alternatively, (4) permits the implicit function theorem, yielding a real-analytic periodic function.

Set
$$
 \gamma=\{\rho(t)e^{it}:t\in\mathbb R\}.
 \tag{5}
$$
Because $\rho$ is positive and continuous, this is the image of a continuous map from the unit circle. If $\rho(t)e^{it}=\rho(u)e^{iu}$, equality of arguments gives $t=u\pmod{2\pi}$. Thus the map is injective, and $\gamma$ is a Jordan curve. It avoids zero and bounds the star-shaped region with radial extent $\rho(t)$.

# Reality of the symbol on the curve

For $z=re^{it}$, direct computation gives
$$
 \begin{aligned}
 \operatorname{Im}a(re^{it})
 &=\left(8r-\frac8r+2r^2\cos t\right)\sin t\\
 &=\frac{8\sin t}{r}\,F(r,t).
 \end{aligned}
 \tag{6}
$$
Equation (6) vanishes identically when $r=\rho(t)$. Hence $a$ is real everywhere on $\gamma$.

Now let
$$
 b(z)=a(z)-a(z)^2.
 \tag{7}
$$
A real polynomial in a real number is real, so $b$ is also real on $\gamma$. Expanding (7) gives exactly (1). Its extreme coefficients are $b_{-2}=-64$ and $b_4=-1$, so the required nonvanishing condition holds with $r=2$, $s=4$.

# A nonreal finite section

Using the repository's indexing convention,
$$
 T_2(b)=\begin{pmatrix}b_0&b_{-1}\\b_1&b_0\end{pmatrix}
       =\begin{pmatrix}-128&8\\-8&-128\end{pmatrix}.
 \tag{8}
$$
Its characteristic polynomial is $(\lambda+128)^2+64$, proving (2) and Theorem 1.

The mechanism is that polynomial composition preserves reality on the curve, whereas finite Toeplitz truncation does not commute with polynomial functional calculus. In particular, $T_2(a-a^2)$ is not required to equal $T_2(a)-T_2(a)^2$.

# Scope and checks

This refutes the assertion about every finite section. It makes no claim to refute a weaker criterion concerning the limiting Toeplitz spectrum; the repository explicitly distinguishes that question.

All coefficients, the finite matrix, its spectrum, and the inequalities establishing the Jordan curve are exact. The verification script also samples the curve, but the curve's existence, injectivity, and reality are proved by (3)--(6), not inferred from a numerical plot.

The repository submission records **Solved**, with a negative-resolution notice and the independent Codex-agent PASS report linked above.

# Sources

[^statement]: *Open Problems in Numerical Linear Algebra*, SP-06, “A real-valued symbol on a Jordan curve and real Toeplitz spectra,” checked 11 September 2026; [canonical entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/SP-06/README.md).

1. *Open Problems in Numerical Linear Algebra*, SP-06, [canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/SP-06/README.md), checked 11 September 2026.
2. B. Shapiro and F. Štampach, *Non-Self-Adjoint Toeplitz Matrices Whose Principal Submatrices Have Real Spectrum*, *Constructive Approximation* 49 (2019), 191--226; [arXiv:1702.00741, version 4](https://arxiv.org/abs/1702.00741v4), including the appended correction, printed pp. 27--28. [Correction DOI](https://doi.org/10.1007/s00365-022-09614-0).
3. D. Giandinoto, *On reality of eigenvalues of banded block Toeplitz matrices*, [arXiv:2411.16266](https://arxiv.org/abs/2411.16266), introduction and §2. These references supply the problem's provenance; the counterexample above is not attributed to them.
