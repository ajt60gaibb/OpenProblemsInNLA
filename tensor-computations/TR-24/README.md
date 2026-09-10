# TR-24 — Degree-five, six, and nine generation of the Salmon tensor ideal

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->

**Difficulty:** extreme  
**Importance:** interesting to specialist  
**Status:** Open  
**Last checked:** 2026-09-10

**Rating rationale:** The remaining ideal-generation assertion is a longstanding barrier in a prominent fixed-format tensor problem. Its precise scheme-theoretic content principally matters to specialists in tensor equations and algebraic statistics.

## Problem statement

Let $V=\mathbb C^4\otimes\mathbb C^4\otimes\mathbb C^4$, with coordinates $t_{ijk}$, and let
$$
X=\overline{\left\{
\sum_{\ell=1}^{4}a_\ell\otimes b_\ell\otimes c_\ell:
a_\ell,b_\ell,c_\ell\in\mathbb C^4
\right\}}^{\,\mathrm{Zar}}\subset V.
$$
Thus $X$ is the affine cone over the fourth secant variety of the Segre embedding of $\mathbb P^3\times\mathbb P^3\times\mathbb P^3$. Its points are exactly the tensors of complex border rank at most four.

Let
$$
I=I(X)=\{f\in\mathbb C[t_{ijk}]: f(T)=0\text{ for every }T\in X\}
$$
be its homogeneous prime ideal. For each integer $a\geq0$, let $I_a$ be the vector space of homogeneous degree-$a$ polynomials in $I$. Is
$$
I=\langle I_5\cup I_6\cup I_9\rangle
$$
as an ideal of $\mathbb C[t_{ijk}]$?

The angle brackets mean all finite polynomial combinations of elements of these three homogeneous spaces. This is the revised Salmon conjecture in the degree-generation form explicitly stated by Friedland–Gross, §1. It asks for equality of ideals, not merely equality of zero sets or equality after taking radicals. It does not prescribe an unverified number of generators or identify the full homogeneous pieces with particular proposed representation modules.

## Why it matters

The question asks for the tensor counterpart of determinantal equations for low-rank matrices. Exact generators describe algebraic constraints in small tensor decompositions and statistical mixture models, and support symbolic and numerical methods for testing and studying these constraints.

## References and status check

1. S. Friedland and E. Gross, *A proof of the set-theoretic version of the Salmon conjecture*, [arXiv:1104.1776v2](https://arxiv.org/pdf/1104.1776v2), §1, p.1, states the revised degree-generation conjecture; Journal of Algebra **356** (2012), 374–379.
2. D. J. Bates and L. Oeding, *Toward a salmon conjecture*, [arXiv:1009.6181v2](https://arxiv.org/pdf/1009.6181v2), introduction pp.1–2 and Theorem 3.10; Experimental Mathematics **20** (2011), 358–370.
3. J. Jagiełła and J. Jelisiejew, *Unrestrictions and concise secant varieties*, [arXiv:2604.24879v2](https://arxiv.org/html/2604.24879v2), §1.5.3, explicitly distinguishes the solved set-theoretic problem from the unknown ideal.

### Status check — 2026-09-10

Checked Friedland–Gross §1 against the displayed ideal equality and Jagiełła–Jelisiejew v2, §1.5.3, together with targeted 2025–2026 Salmon-ideal searches. The 2026 source explicitly retains the ideal question. The proved equality of zero sets only identifies the radical of the proposed ideal; it does not settle a portion of this fixed ideal-equality assertion. Numerical or local vanishing and dimension certificates likewise do not prove ideal equality. No complete proof was located, so the status remains Open.
