---
title: "SP-04: A generic counterexample to the smallest-absolute-multiplier rule"
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Proposed resolution, not independently verified.  
**Outcome claimed:** Negative resolution claim.  
**Prepared:** 11 September 2026.  
**Target:** [Repository entry SP-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/SP-04/README.md), snapshot `b412319`.

This is a proposed argument generated in a ChatGPT conversation and prepared for mathematical review. No independent referee report or formal proof certificate accompanies it. Supporting algebraic and numerical diagnostics are not a substitute for proof review. No publication or priority claim is made.

## Theorem SP-04: proposed generic counterexample

For real data $U$, consider real stationary pairs
$$
|\det X|=1,\qquad X^T(U-X)=cI.
$$
The rule under consideration selects a pair with smallest $|c|$ and claims that its matrix is nearest to $U$ in Frobenius norm.

**Claim.** The rule fails for every diagonal matrix
$$
U=\operatorname{diag}(s_1,s_2,s_3),\qquad
\frac74<s_1<s_2<s_3<\frac{44}{25}.
$$
It therefore fails on a nonempty open set of real $3\times3$ matrices and cannot hold outside a proper real algebraic exceptional set.

### 1. Reduction of all stationary matrices

Write $S=X^TX$. The stationary equation gives
$$
U=X+cX^{-T},\qquad U^TU=S+2cI+c^2S^{-1}.
$$
Thus $S$ commutes with $U^TU$. The latter is diagonal with distinct entries, so $S$ is diagonal. Also
$$
U=X(I+cS^{-1}).
$$
The second factor is invertible, because both $U$ and $X$ are invertible. Hence $X$ is diagonal as well. Writing its entries as $x_i$, every stationary pair satisfies
$$
x_i^2-s_ix_i+c=0,\qquad |x_1x_2x_3|=1.
$$

### 2. No stationary pair has $0\le c\le13/25$

If $c=0$, invertibility forces $X=U$, whose determinant exceeds one. For $0<c\le13/25=0.52$, write
$$
r_i(c)=\frac{s_i+\sqrt{s_i^2-4c}}2.
$$
The two roots are $r_i$ and $c/r_i$, both positive. Throughout this range, $r_{\min}>1$ and $r_{\max}\le1.76$. For example,
$$
r_{\min}>\frac{1.75+\sqrt{1.75^2-4(0.52)}}2>1.
$$
Moreover,
$$
\frac{\partial r}{\partial s}
=\frac12\left(1+\frac{s}{\sqrt{s^2-4c}}\right)<2,
$$
since $s^2-4c\ge0.9825$ and $s\le1.76$. The interval of possible $s_i$ has width $0.01$, so
$$
r_{\max}-r_{\min}<0.02,\qquad
\frac{r_{\max}}{r_{\min}}<1.02.
$$
Choosing three large roots gives product greater than one. Any selection containing a small root has product at most the largest product with exactly one small root, since replacing a small root by its large partner increases the product. That product is bounded by
$$
c\frac{r_{\max}^2}{r_{\min}}
<0.52(1.76)(1.02)=0.933504<1.
$$
No root selection has product one.

### 3. The unique least absolute multiplier is negative

Set $c=-t$, $t>0$, and put
$$
a_i(t)=\frac{s_i+\sqrt{s_i^2+4t}}2.
$$
The two roots are $a_i(t)$ and $-t/a_i(t)$. Choose the negative root only at the first index. The absolute determinant is
$$
g(t)=\frac{t}{a_1(t)}a_2(t)a_3(t).
$$
Every factor is strictly increasing for $t>0$: in particular,
$$
\frac{t}{a_i(t)}=\frac{\sqrt{s_i^2+4t}-s_i}{2}.
$$
The continuous function $g$ is strictly increasing from zero. At $t=0.52$, the positive roots exceed two, because $4-2s_i-0.52<0$. The magnitude of the negative root exceeds $1/4$, since
$$
(1/4)^2+s_1/4<\frac1{16}+\frac{1.76}{4}=0.5025<0.52.
$$
Consequently $g(0.52)>1$, and there is a unique $t_*\in(0,0.52)$ with $g(t_*)=1$.

For a nonempty set $E$ of negative-root indices, the absolute determinant at fixed $t>0$ is
$$
a_1a_2a_3\prod_{i\in E}\frac{t}{a_i^2}.
$$
Each extra factor is strictly between zero and one, and the largest factor is uniquely $t/a_1^2$, since $a_1<a_2<a_3$. Thus, among all nonempty negative-root patterns, the absolute determinant is uniquely largest for $E=\{1\}$. Each pattern's product increases strictly with $t$ and tends to infinity. All other patterns therefore reach one strictly after $t_*$. The all-positive pattern has product greater than one for every $t>0$ and gives no such stationary pair.

Together with the exclusion of $0\le c\le0.52$, this proves that $c_*=-t_*$ is the unique smallest-absolute stationary multiplier.

### 4. Failure of nearestness and the generic qualifier

At this selected pair, $x_1<0$ and the other two entries are positive. Replacing $x_1$ by $|x_1|$ preserves $|\det X|=1$ and reduces the squared distance by
$$
(s_1-x_1)^2-(s_1-|x_1|)^2=4s_1|x_1|>0.
$$
The selected matrix is therefore not nearest.

For the concrete rational data
$$
(s_1,s_2,s_3)=(1751,1755,1759)/1000,
$$
the diagnostic numerical values are
$$
\begin{aligned}
c_*&\approx-0.497407247776,\\
(x_1,x_2,x_3)&\approx(-0.24873641,\ 2.00329461,\ 2.00685420),\\
\|U-X_*\|_F^2&\approx4.122027613290.
\end{aligned}
$$
The feasible matrix $I_3$ already has smaller squared distance $1.710107$. These decimals illustrate the exact inequalities above; they are not used as proof.

Finally, if $U=P\operatorname{diag}(s)Q^T$ is a singular-value decomposition, the transformation $Y=P^TXQ$ preserves $|\det X|$, the Frobenius objective, and the stationary multiplier:
$$
Y^T(\operatorname{diag}(s)-Y)=Q^TX^T(U-X)Q=cI.
$$
The same failure occurs for every real matrix with distinct singular values in $(7/4,44/25)$. This set is nonempty and open. A proper real algebraic set has empty Euclidean interior, so algebraic genericity cannot exclude all these counterexamples. $\square$

## Scope and review notes

Both determinant signs are included, as required by the entry. The proof gives a unique least absolute multiplier and extends from diagonal data to an open set of matrices with distinct singular values. This addresses the stated algebraic-generic qualifier rather than only an exceptional example. No claim is made about a different projection problem restricted to determinant +1.

The main review points are the reduction of every stationary matrix (not just a diagonal candidate), uniqueness of the smallest absolute multiplier, and the passage to an open set under left/right orthogonal transformations.

The packaging pass checked the repository statement and contribution rules on 11 September 2026. It did not conduct a new exhaustive literature search or establish novelty.

## Source references

Alex Townsend, *Open Problems in Numerical Linear Algebra* (2026), [entry SP-04](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/SP-04/README.md), repository snapshot `b412319`, accessed 11 September 2026.

J. A. Baaijens and J. Draisma, *Euclidean distance degrees of real algebraic groups*, *Linear Algebra and its Applications* 467 (2015), 174–187, §4.1 and Problem 4.3 on p. 186, [DOI](https://doi.org/10.1016/j.laa.2014.11.012). The catalog also cites P. Jaap and O. Sander, *How to project onto SL(n)*, [arXiv:2501.19310](https://arxiv.org/abs/2501.19310), introduction, for the related determinant-one problem. Source locators are those recorded by the catalog.
