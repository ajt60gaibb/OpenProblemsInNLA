# MI-13 — Nobori's spectral-middle-factor commutator conjecture

**Difficulty:** challenging  
**Importance:** interesting to specialist  
**Provenance:** explicit conjecture  
**Status:** Solved  
**Last checked:** 2026-09-10

**Resolution — affirmative, 2026-09-10:** The exact statement follows from the established complex refined commutator inequality. The complete reduction is given below. This is a repository proof checked independently by two additional Codex agents; it has not received external peer review or Lean formalization. No claim of novelty is made.

**Rating rationale:** The difficulty label is retained as the historical pre-resolution assessment; it is no longer an estimate of open work. The impact is a specific rectangular commutator inequality, hence specialist.

## Problem statement

Let $`m,n\ge2`$ be integers. For every $`A,C\in\mathbb C^{m\times n}`$ and $`B\in\mathbb C^{n\times m}`$, is

```math
\|ABC-CBA\|_F^2\le
2\|B\|_2^2\bigl(\sigma_1(A)^2+\sigma_2(A)^2\bigr)\|C\|_F^2?
```

Here $`\|X\|_F=(\mathop{\mathrm{tr}}\nolimits(X^*X))^{1/2}`$, $`\|X\|_2=\sigma_1(X)`$, and $`\sigma_1(X)\ge\sigma_2(X)\ge\cdots`$ are the singular values. Zero matrices and deficient ranks are allowed.

## Relevance

The expression measures failure of two rectangular factors to commute through a middle map. A bound using the middle factor's operator norm and only two singular values of an outer factor would sharpen estimates for products of rectangular matrices.

## References

1. M. Nobori, *A generalization of the Böttcher–Wenzel inequality for three rectangular matrices*, Linear Algebra and its Applications 725 (2025), 135–144. Conjecture 3.1, equation (8), in [arXiv:2506.17365v2](https://arxiv.org/html/2506.17365v2); [journal](https://doi.org/10.1016/j.laa.2025.07.005).
2. M. Nobori, *A note on some upper bounds for the Frobenius norm of the $`q`$-deformed commutator*, arXiv:2608.03897v1 (2026), Theorem 1.1 and §3. [Primary manuscript](https://arxiv.org/html/2608.03897v1).

3. K. M. R. Audenaert, *Variance bounds, with an application to norm bounds for commutators*, Linear Algebra Appl. 432(5) (2010), 1126–1143; preprint §7.4, Corollary 5, manuscript p. 25. [Primary manuscript](https://arxiv.org/pdf/0907.3913).

## Resolution proof — 2026-09-10

Write $`s_2(X)=(\sigma_1(X)^2+\sigma_2(X)^2)^{1/2}`$.
The established complex refined commutator inequality is

```math
\|[X,Y]\|_F\le\sqrt2\,s_2(X)\|Y\|_F,
\qquad X,Y\in\mathbb C^{r\times r},\quad r\ge2.\tag{1}
```

This is Audenaert's Corollary 5, with the two arguments interchanged; his
$`\|\cdot\|_2`$ denotes the Frobenius norm and his $`\|\cdot\|_{(2),2}`$ is $`s_2`$.
It also follows from Nobori's proved Theorem 1.1 by making its third matrix the
identity. Neither route assumes Nobori's Conjecture 3.1.

First suppose $`A,B,C`$ are square of order $`r`$. For every unitary $`U`$,

```math
(AUC-CUA)U=[AU,CU].
```

Unitary invariance and (1) therefore give

```math
\|AUC-CUA\|_F\le\sqrt2\,s_2(A)\|C\|_F.\tag{2}
```

If $`\|B\|_2\le1`$, choose a singular value decomposition $`B=P D Q^*`$, with
$`P,Q`$ unitary and $`D`$ real diagonal with entries in $`[0,1]`$. Define

```math
U_\pm=P\bigl(D\pm i\sqrt{I-D^2}\bigr)Q^*.
```

Each diagonal entry of $`D\pm i\sqrt{I-D^2}`$ has modulus one, so $`U_+`$ and
$`U_-`$ are unitary and $`B=(U_++U_-)/2`$. Linearity in $`B`$, the triangle
inequality, and (2) yield

```math
\|ABC-CBA\|_F
\le\frac{\|AU_+C-CU_+A\|_F+\|AU_-C-CU_-A\|_F}{2}
\le\sqrt2\,s_2(A)\|C\|_F.
```

For arbitrary nonzero $`B`$, apply this result to $`B/\|B\|_2`$ and rescale.
The case $`B=0`$ is immediate. This proves the claimed unsquared bound for square matrices.

For the rectangular case, put $`r=\max(m,n)`$ and let
$`E\in\mathbb C^{r\times m}`$ and $`F\in\mathbb C^{r\times n}`$ be coordinate
inclusions, so $`E^*E=I_m`$ and $`F^*F=I_n`$. Set

```math
\widetilde A=EAF^*,\qquad
\widetilde B=FBE^*,\qquad
\widetilde C=ECF^*.
```

These are square matrices of order $`r`$, and

```math
\widetilde A\widetilde B\widetilde C-
\widetilde C\widetilde B\widetilde A=E(ABC-CBA)F^*.
```

The inclusions preserve Frobenius and operator norms and add only zero singular
values. Thus $`s_2(\widetilde A)=s_2(A)`$, including when the rank is below two.
Apply the square result and square its nonnegative sides to obtain exactly

```math
\|ABC-CBA\|_F^2\le
2\|B\|_2^2\bigl(\sigma_1(A)^2+\sigma_2(A)^2\bigr)\|C\|_F^2.
```

This covers every displayed dimension and factor, without invertibility or
reality assumptions. The constant two is attained for $`m=n=2`$,
$`A=\mathop{\mathrm{diag}}\nolimits(1,-1)`$, $`B=I_2`$ and $`C=e_{12}`$: both sides equal four.

## Status evidence and verification scope

Nobori's source still labels the target Conjecture 3.1. A bounded search found
no separate published resolution, but the explicit argument above changes this
catalog's status. The audit checked the complex field in (1), the norm
conventions, unitary invariance, the two-unitary decomposition, scaling at
$`B=0`$, preservation of rectangular products and singular values, and sharpness.
Two independent agent reviews accepted the reduction. The published commutator
theorem is the external dependency; the new reduction is not a claim of an
externally refereed theorem. The original target is retained and excluded from
the open count.

<!-- navigation -->
[All categories](../../README.md) · [Category index](../README.md) · [Read PDF](problem.pdf) · [LaTeX source](problem.tex)
<!-- /navigation -->
