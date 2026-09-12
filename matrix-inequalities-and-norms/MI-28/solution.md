---
title: "MI-28: a determinant inequality for all nonnegative base powers"
author: "George Stepaniants"
affiliation: "Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA"
date: "11 September 2026"
document-kind: "Verified resolution"
review-footer: "Independent Codex-agent review; not external human peer review or formal certification."
---

\pagestyle{plain}

For positive definite matrices $A,B$, every $k\ge0$, and $0\le p\le2$, we prove

$$
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p).
$$

In fact, a log-majorization of the corresponding normalized matrices holds. The previously proved range $k\ge2$ is due to Ghabries, Abbas, Mourad, and Assi. We treat the remaining base powers using a normalized order implication. Two applications of the Furuta inequality establish complementary parameter regions. The identity $\lvert |AB|^{-1}B\rvert=A^{-1}$ interchanges the two parameters and closes the remaining range.

**Verification status: independent-agent PASS.** Developed with substantial ChatGPT/Codex assistance. A separate agent audited the complete analytic argument, its parameter ranges and its primary-source applications. [Detailed independent review](../../references/stepaniants-mi28-2026-09-11/verification/reviews/MI-28-review.md). This is independent agent review, not external human peer review or formal verification.

## Statement and notation

Throughout, $A,B\in\mathbb C^{n\times n}$ are positive definite, matrix powers are defined by spectral functional calculus, and $\|\cdot\|$ denotes the operator norm. For a matrix $M$, write $|M|=(M^*M)^{1/2}$. Eigenvalues of a positive definite matrix are listed in decreasing order. For positive vectors $u,v\in(0,\infty)^n$, the notation $u\prec_{\log}v$ means

$$
\prod_{i=1}^j u_i\le\prod_{i=1}^j v_i\quad(1\le j<n),
\qquad
\prod_{i=1}^n u_i=\prod_{i=1}^n v_i.
$$

### Theorem 1 — The full determinant and log-majorization inequalities

For every $A,B>0$, $k\ge0$, and $0\le p\le2$,

$$
\lambda\!\left(A^{(p-k)/2}B^pA^{(p-k)/2}\right)
\prec_{\log}
\lambda\!\left(A^{-k/2}|AB|^pA^{-k/2}\right).
$$

Consequently,

$$
\det(A^k+|AB|^p)\ge\det(A^k+A^pB^p).
$$

The determinant inequality is the positive definite formulation of [MI-28](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-28/README.md), originating in [Ghabries's thesis](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications), §2.5 and final Open Problems, Problem 1, pp. 109–110. Although $A^k+A^pB^p$ need not be Hermitian, its determinant is positive: after factoring out $A^k$, the remaining product $A^{p-k}B^p$ is similar to the positive definite matrix on the left of the log-majorization. The range $k\ge2$, $0\le p\le2$ follows already from [Ghabries–Abbas–Mourad–Assi, Lemma 2.5](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality); the precise substitution appears in the proof of Theorem 1 below.

## Two order implications

We use the Löwner–Heinz inequality

$$
0<X\le Y,\quad 0\le t\le1
\quad\Longrightarrow\quad X^t\le Y^t,
$$

and the following convention for the Furuta inequality: if $X\ge Y>0$, $r\ge0$, $a\ge0$, $q\ge1$, and $(1+r)q\ge a+r$, then

$$
(X^{r/2}Y^aX^{r/2})^{1/q}\le X^{(a+r)/q}.
$$

Furuta's original paper is listed in the references. Both facts are also restated in [Tanahashi, Propositions 1–2](https://www.researchgate.net/publication/255605812_The_Furuta_inequality_with_negative_powers). The $r$ used here is twice the sandwich exponent in that reference.

For $k,p>0$, let $\mathcal I(k,p)$ denote the assertion that, for every $A,B>0$, with $D=|AB|$,

$$
D^p\le A^k\quad\Longrightarrow\quad B^p\le A^{k-p}.
$$

This notation describes a universal order implication. It makes no assumption that $A$ and $B$ commute.

### Lemma 2 — The lower-power Furuta implication

If $k>0$ and $k/(k+1)\le p\le1$, then $\mathcal I(k,p)$ holds.

**Proof.** Assume $D^p\le A^k$. In the Furuta inequality, choose

$$
X=A^k,\qquad Y=D^p,\qquad r=\frac2k,\qquad
a=\frac2p,\qquad q=2.
$$

The condition $(1+r)q\ge a+r$ is exactly $p\ge k/(k+1)$. Thus

$$
(AD^2A)^{1/2}\le A^{1+k/p}.
$$

Since $D^2=BA^2B$, we have $AD^2A=(ABA)^2$, and its positive square root is $ABA$. Congruence by $A^{-1}$ gives $B\le A^{k/p-1}$. Applying Löwner–Heinz with exponent $p\in(0,1]$ proves $B^p\le A^{k-p}$. $\square$

### Lemma 3 — The higher-power Furuta implication

If $k>0$ and $1\le p\le2$, then $\mathcal I(k,p)$ holds.

**Proof.** Assume $D^p\le A^k$, and set

$$
C=ABA,\qquad s=\frac{p(k+2)}{k+p}.
$$

The hypotheses give $1\le p\le s\le2$. Apply the Furuta inequality with

$$
X=A^k,\qquad Y=D^p,\qquad r=\frac2k,\qquad
a=\frac2p,\qquad q=\frac2s.
$$

Here $q\ge1$ and $(1+r)q=a+r$. Using $AD^2A=C^2$, we obtain

$$
C^s=(AD^2A)^{s/2}\le A^{k+2}.
$$

Because $0<2/(k+2)\le1$, Löwner–Heinz followed by inversion gives

$$
A^{-2}\le C^{-2s/(k+2)}=C^{-2p/(k+p)}.
$$

For every invertible $S$ and real $p$, a singular-value decomposition gives

$$
(SS^*)^p=S(S^*S)^{p-1}S^*.
$$

Apply this identity to $S=A^{-1}C^{1/2}$, for which $SS^*=B$:

$$
B^p=A^{-1}C^{1/2}
(C^{1/2}A^{-2}C^{1/2})^{p-1}
C^{1/2}A^{-1}.
$$

Congruence in the inequality for $A^{-2}$, followed by Löwner–Heinz with $0\le p-1\le1$, therefore yields

$$
\begin{aligned}
B^p
&\le A^{-1}C^{\,1+(p-1)(k-p)/(k+p)}A^{-1}\\
&=A^{-1}C^{\,p(k-p+2)/(k+p)}A^{-1}.
\end{aligned}
$$

The exponent of $C$ in the last line equals $s\theta$, where

$$
\theta=\frac{k-p+2}{k+2}\in[0,1].
$$

Applying Löwner–Heinz to $C^s\le A^{k+2}$ gives $C^{s\theta}\le A^{k-p+2}$. Substitute this in the bound for $B^p$ to conclude $B^p\le A^{k-p}$. $\square$

**Remark 4 — Relation to the negative-power Furuta inequality.** The argument after $C^s\le A^{k+2}$ is a direct proof of the needed specialization of the negative-power Furuta inequality. In the convention used here, the relevant parameters in [Tanahashi, Theorem 3](https://www.researchgate.net/publication/255605812_The_Furuta_inequality_with_negative_powers) are

$$
X=A^{k+2},\quad Y=C^s,\quad
a=\frac{k+p}{p(k+2)},\quad q=\frac1p,\quad r=-\frac2{k+2}.
$$

The displayed proof verifies that specialization using only Löwner–Heinz and the singular-value identity.

## Interchanging the parameters

### Lemma 5 — The parameter swap

Let $0<p\le k$. If $\mathcal I(p,k)$ holds, then $\mathcal I(k,p)$ holds.

**Proof.** Assume $D^p\le A^k$, where $D=|AB|$, and define

$$
\widetilde A=D^{-1},\qquad \widetilde B=B.
$$

The order of the factors is essential. Directly,

$$
|\widetilde A\widetilde B|^2
=BD^{-2}B
=B(B^{-1}A^{-2}B^{-1})B
=A^{-2},
$$

so $|\widetilde A\widetilde B|=A^{-1}$. Inverting the assumed order gives

$$
|\widetilde A\widetilde B|^k=A^{-k}
\le D^{-p}=\widetilde A^p.
$$

Apply $\mathcal I(p,k)$ to this pair:

$$
B^k\le\widetilde A^{p-k}=D^{k-p}.
$$

Since $0<p/k\le1$, Löwner–Heinz applied to this inequality gives

$$
B^p\le D^{p(k-p)/k}.
$$

Since $0\le(k-p)/k\le1$, applying it also to $D^p\le A^k$ gives

$$
D^{p(k-p)/k}\le A^{k-p}.
$$

Together these inequalities prove $\mathcal I(k,p)$. If $p=k$, the second exponent is zero and its inequality is simply $I\le I$; the argument still applies. $\square$

### Corollary 6 — All base powers up to two

For $0<k\le2$ and $0<p\le2$, the implication $\mathcal I(k,p)$ holds.

**Proof.** If $p\ge1$, use Lemma 3. Suppose $0<p<1$. If $p\ge k/(k+1)$, use Lemma 2. In the remaining case,

$$
p<\frac{k}{k+1}<k\le2.
$$

We establish the swapped implication $\mathcal I(p,k)$. When $k\le1$, its exponent $k$ satisfies

$$
\frac{p}{p+1}<p<k\le1,
$$

so Lemma 2, with the parameters interchanged, applies. When $1\le k\le2$, Lemma 3, with the parameters interchanged, applies. Lemma 5 now proves $\mathcal I(k,p)$. $\square$

## Log-majorization and the determinant

**Proof of Theorem 1.** First take $0<k\le2$, $0<p\le2$, and write

$$
H=A^{(p-k)/2}B^pA^{(p-k)/2},\qquad
Z=A^{-k/2}D^pA^{-k/2}.
$$

Both matrices are homogeneous of degree $p$ in $B$. Let $c=\|Z\|>0$, and replace $B$ by $c^{-1/p}B$. The resulting $Z$ is at most $I$, equivalently $D^p\le A^k$ for the scaled pair. Corollary 6 gives $B^p\le A^{k-p}$. Congruence by $A^{(p-k)/2}$ shows that the scaled $H$ is at most $I$. Scaling back proves

$$
\|H\|\le\|Z\|.
$$

For every $1\le j\le n$, apply this norm inequality to $\bigwedge^j A$ and $\bigwedge^j B$. These exterior powers are positive definite and preserve products, inverses, and spectral powers. In particular,

$$
\left|(\bigwedge\nolimits^j A)(\bigwedge\nolimits^j B)\right|
=\bigwedge\nolimits^j |AB|.
$$

The operator norm of an exterior power of a positive definite matrix is the product of its $j$ largest eigenvalues. We thus obtain all partial-product inequalities in the claimed log-majorization. The full determinants agree:

$$
\det H=\det Z=\det(A)^{p-k}\det(B)^p.
$$

This proves the log-majorization for $0<k\le2$, $0<p\le2$.

For $k\ge2$, use the previously established result [Ghabries–Abbas–Mourad–Assi, Lemma 2.5](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality). In its notation, for $0\le t\le s\le K$,

$$
\lambda(X^{K-t}Y^t)
\prec_{\mathrm{wlog}}
\lambda\!\left(
X^{K/2}(Y^{s/2}X^{-s}Y^{s/2})^{t/s}X^{K/2}\right).
$$

Take $X=A^{-1}$, $Y=B$, $K=k$, $s=2$, and $t=p$. The two eigenvalue lists are exactly those of $H$ and $Z$; the product $A^{p-k}B^p$ is similar to $H$. Equality of the full determinants changes this weak log-majorization into the claimed log-majorization. This invokes the original range $0\le t\le s\le K$ without altering any of its parameter restrictions.

When $p=0$, the two matrices in the claimed log-majorization are both $A^{-k}$, so equality holds. For $k=0$, $p>0$, let $k\downarrow0$ in the established range $0<k\le2$. Functional calculus and the ordered eigenvalues are continuous on the positive definite cone, and each partial-product inequality and the equality of the full determinants persists. Thus the log-majorization holds at every stated endpoint.

Finally, log-majorization is ordinary majorization of the logarithms of the eigenvalues. Applying the convex function $t\mapsto\log(1+e^t)$ gives

$$
\det(I+H)\le\det(I+Z).
$$

Indeed, the corresponding inequality for the sums of this convex function is the standard convex-function characterization of majorization. Since $A^{p-k}B^p$ is similar to $H$,

$$
\begin{aligned}
\det(A^k+A^pB^p)&=\det(A^k)\det(I+H),\\
\det(A^k+D^p)&=\det(A^k)\det(I+Z).
\end{aligned}
$$

Multiplying by the positive number $\det(A^k)$ proves the determinant inequality. $\square$

**Remark 7 — Scope.** The theorem treats every dimension and every parameter pair in the canonical positive definite statement of MI-28. For $k>0$ and $p>0$, the positive semidefinite extension follows by applying the determinant inequality to $A+\varepsilon I$ and $B+\varepsilon I$, then letting $\varepsilon\downarrow0$. The positive definite formulation avoids conventions for zeroth powers of singular matrices.

## References

1. **MI-28.** ajt60gaibb/OpenProblemsInNLA. *Ghabries's determinant comparison for arbitrary nonnegative base powers*. [Canonical problem statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/matrix-inequalities-and-norms/MI-28/README.md).

2. **Ghabries's thesis.** M. M. Ghabries. *Contributions to Matrix Inequalities and Some Applications*. PhD thesis, University of Angers and Lebanese University, 2022. Section 2.5 and final Open Problems, Problem 1, pp. 109–110. [Author-uploaded thesis](https://www.researchgate.net/publication/361793582_Contributions_to_Matrix_Inequalities_and_Some_Applications).

3. **Ghabries–Abbas–Mourad–Assi (2020).** M. M. Ghabries, H. Abbas, B. Mourad, and A. Assi. *A proof of a conjectured determinantal inequality*. Linear Algebra and its Applications **605** (2020), 21–28. Lemma 2.5 and Theorem 1.1. [DOI: 10.1016/j.laa.2020.07.013](https://doi.org/10.1016/j.laa.2020.07.013); [author-uploaded full text](https://www.researchgate.net/publication/342908148_A_proof_of_a_conjectured_determinantal_inequality).

4. **Furuta (1987).** T. Furuta. *$A\ge B\ge O$ assures $(B^rA^pB^r)^{1/q}\ge B^{(p+2r)/q}$ for $r\ge0$, $p\ge0$, $q\ge1$ with $(1+2r)q\ge p+2r$*. Proceedings of the American Mathematical Society **101** (1987), 85–88.

5. **Tanahashi (1999).** K. Tanahashi. *The Furuta inequality with negative powers*. Proceedings of the American Mathematical Society **127** (1999), 1683–1692. Propositions 1–2 and Theorem 3. [DOI: 10.1090/S0002-9939-99-04705-X](https://doi.org/10.1090/S0002-9939-99-04705-X); [author-uploaded full text](https://www.researchgate.net/publication/255605812_The_Furuta_inequality_with_negative_powers).
