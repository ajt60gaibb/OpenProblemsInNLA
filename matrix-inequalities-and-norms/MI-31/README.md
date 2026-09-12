# MI-31 — Sharp parameter dependence for structured Gaussian operator norms

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Topic:** Expected norms of random matrices with unequal entry variances  
**Difficulty:** challenging  
**Importance:** interesting to the community  
**Status:** Partially resolved  
**Last checked:** 2026-09-11

**Rating rationale:** The expectation is characterized for fixed norm exponents, but making the constant uniform requires sharper control as the exponents and dimensions vary. Such estimates quantify amplification by random matrices under different input and output norms.

## Statement

Let $m,n$ be positive integers, $1\le p\le2\le q\le\infty$, and
$A=(a_{ij})\in\mathbb R^{m\times n}$. Let $p^*$ satisfy $1/p+1/p^*=1$,
with $p^*=\infty$ when $p=1$, and set $L(k)=\max\{1,\ln k\}$ for integers
$k\ge1$. For independent standard real Gaussian variables $g_{ij}$, set
$G_A=(a_{ij}g_{ij})$. Define

$$
\|B\|_{p\to q}=\sup_{\|x\|_p\le1}\|Bx\|_q,
\qquad
D_1=\max_{1\le i\le m}\|(a_{ij})_{j=1}^n\|_{p^*},
\qquad
D_2=\max_{1\le j\le n}\|(a_{ij})_{i=1}^m\|_q.
$$

**Conjecture (Latała–Strzelecka).** There is an absolute constant $C>0$,
independent of $m,n,p,q,A$, such that

$$
\mathbb E\|G_A\|_{p\to q}
\le C\left[
\sqrt{\min\{p^*,L(n)\}}\,D_1
+\sqrt{\min\{q,L(m)\}}\,D_2
+\mathbb E\max_{i,j}|a_{ij}g_{ij}|
\right].
$$

Use the usual maximum norm for an $\ell_\infty$ vector norm and
$\min\{\infty,L(k)\}=L(k)$. The conjecture is a uniform upper bound;
it does not assert a matching lower bound with these same three terms for
every variance profile.

## Known cases and numerical significance

The spectral case $p=q=2$ is known. For $a_{ij}=1$ throughout, the two
dimension-capped square-root factors have the correct order. The same paper
proves comparison with $D_1+D_2+\mathbb E\max_{i,j}|a_{ij}g_{ij}|$ using
constants allowed to depend on $p,q$. That theorem resolves the older
Guédon–Hinrichs–Litvak–Prochno conjecture, while the displayed universal
constant remains the new target.

The matrix $G_A$ models independent random entry errors with a prescribed
variance profile. Its induced norm measures worst-case amplification from
an input $\ell_p$ norm to an output $\ell_q$ norm. The parameter dependence
matters when the norms themselves vary with dimension.

## References and status check

- R. Latała and M. Strzelecka, *Operator $\ell_p\to\ell_q$ norms of Gaussian matrices*, Advances in Mathematics 501 (2026), article 111097. [DOI](https://doi.org/10.1016/j.aim.2026.111097); [current arXiv v3](https://arxiv.org/html/2502.02186v3), dated 2026-06-09. Conjecture 5 is the displayed upper bound; the notation preceding Conjecture 1 defines the absolute implicit constant and the truncated logarithm. Theorem 2 and Remarks 3–4 distinguish the proved comparison from the conjectured parameter dependence.
- R. Latała, R. van Handel and P. Youssef, *The dimension-free structure of nonhomogeneous random matrices*, Inventiones Mathematicae 214 (2018), 1031–1080. The spectral-norm result is identified as reference 15 in the preceding source.

On 2026-09-11, checked the current arXiv version and published full text,
the authors' institutional publication records, and exact-title,
author/Conjecture-5, sharp-parameter-dependence, proof and counterexample
searches through 2026. No full resolution of Conjecture 5 was located.
Statements that the older Conjecture 1 has been solved do not settle this
uniform-constant refinement. This is a bounded literature check.
