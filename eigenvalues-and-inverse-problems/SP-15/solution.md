---
title: 'SP-15: An infinite fiber of shifted singular-value data'
author: 'George Stepaniants'
affiliation: 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
date: '12 September 2026 (UTC)'
document-kind: 'NEGATIVE RESOLUTION'
review-footer: 'Substantial AI assistance; independent automated review is documented separately.'
---

This manuscript answers the complete [SP-15 question](README.md) negatively in dimension nine. The original question and generic finiteness theorem are due to Maxime Fortier Bourque and Thomas Ransford. The argument below is an existence proof of a continuous exceptional fiber, using an exact block determinant identity and the smooth constant-rank theorem.

**Independent review.** A separate [Codex-agent mathematical audit](../../references/stepaniants-sp15-2026-09-12/verification/independent-review-aa01/review.md) returned PASS for the complete negative resolution, with no mathematical correction. The [submission record](../../references/stepaniants-sp15-2026-09-12/README.md) preserves the exact frozen source and signed reports. Substantial AI assistance is disclosed; this is informal automated review, not external human peer review or formal verification.

## Exact target and conclusion

SP-15 asks whether for each complex matrix order $N$ there is a finite uniform bound on the number of unitary similarity classes sharing all the singular values of $A-zI$, for every $z\in\mathbb C$.

**Theorem.** There is a nonconstant smooth one-parameter family of complex $9\times9$ matrices whose members have the same singular values for every complex scalar shift, and no two distinct members are unitarily similar. Each member is nilpotent of index three, with Jordan type $(3,3,3)$. Consequently no integer $M_9$ with the property required in SP-15 exists, and the proposed assertion for every $N$ is false.

The construction is an existence argument using a polynomial coefficient map and the constant-rank theorem. It does not require a numerical search, and does not assert a specific numerical choice of the fixed data fiber.

## 1. A three-block family and its shifted determinant

Let $r\geq1$, and let $P,Q\in\mathbb C^{r\times r}$ be positive definite Hermitian matrices. Put $X=P^{1/2}$, $Y=Q^{1/2}$, where both roots are the positive definite Hermitian roots, and define

$$
A(P,Q)=\begin{pmatrix}0&X&0\\0&0&Y\\0&0&0\end{pmatrix}.
$$

For real $t>0$ and $z\in\mathbb C$, write $s=t+|z|^2$ and $K=s^2I_r+tP$. Direct block multiplication gives

$$
tI_{3r}+(A-zI_{3r})^*(A-zI_{3r})
=\begin{pmatrix}
sI_r&-\overline zX&0\\
-zX^*&sI_r+P&-\overline zY\\
0&-zY^*&sI_r+Y^*Y
\end{pmatrix}.
$$

Eliminating the first block leaves a middle diagonal block

$$
sI_r+P-\frac{|z|^2}{s}P
=sI_r+\frac tsP=\frac Ks.
$$

Both $sI_r$ and $K$ are positive definite. Taking the next Schur complement and using $YY^*=Q$ gives

$$
\begin{aligned}
&\det\bigl[tI_{3r}+(A-zI_{3r})^*(A-zI_{3r})\bigr]\\
&\qquad=\det K\,
\det\bigl[sI_r+Y^*(I_r-|z|^2sK^{-1})Y\bigr]\\
&\qquad=\det K\,
\det\bigl[sI_r+(I_r-|z|^2sK^{-1})Q\bigr]\\
&\qquad=\det\bigl[sK+(K-|z|^2sI_r)Q\bigr]\\
&\qquad=\det\bigl[s^3I_r+st(P+Q)+tPQ\bigr].
\end{aligned}
$$

The second equality uses $\det(sI+BC)=\det(sI+CB)$; the third multiplies the matrix inside the determinant on the left by $K$. The final equality uses $s-|z|^2=t$. No commutativity of $P$ and $Q$ is required.

Define the two-variable polynomial

$$
F_{P,Q}(u,s)=\det\bigl[uI_r+s(P+Q)+PQ\bigr].
$$

The determinant identity becomes

$$
\det\bigl[tI_{3r}+(A(P,Q)-zI_{3r})^*(A(P,Q)-zI_{3r})\bigr]
=t^r F_{P,Q}(s^3/t,s),\qquad t>0.
$$

Therefore equality of $F_{P,Q}$ for two pairs implies equality of the Gram characteristic polynomials for every $z$: for fixed $z$, the displayed determinant polynomials agree for all $t>0$, hence identically. Their roots are the negatives of the squared singular values, with multiplicities. Thus equal $F$ implies equality of every shifted singular value, exactly as required by the definition in SP-15.

## 2. The data consists of at most nine real numbers when $r=3$

The total degree of $F_{P,Q}(u,s)$ is at most $r$, and its $u^r$ coefficient is identically one. All its coefficients are real. To see the latter point, for real $u,s$ write

$$
uI_r+s(P+Q)+PQ=(P+sI_r)(Q+sI_r)+(u-s^2)I_r.
$$

Taking the conjugate transpose reverses the two Hermitian factors. The identity

$$
\det(BC+cI_r)=\det(CB+cI_r)
$$

shows that the determinant equals its complex conjugate. A polynomial which is real on all of $\mathbb R^2$ has real coefficients.

When $r=3$, the monomials of total degree at most three are

$$
1,\ u,\ s,\ u^2,\ us,\ s^2,\ u^3,\ u^2s,\ us^2,\ s^3.
$$

There are ten monomials and the coefficient of $u^3$ is fixed. Thus the other nine real coefficients give a map into $\mathbb R^9$ which determines all shifted singular values of $A(P,Q)$.

## 3. Ten parameters with no repeated unitary class

Take $r=3$ and restrict to

$$
P=\operatorname{diag}(p_1,p_2,p_3),\qquad 0<p_1<p_2<p_3,
$$

and

$$
Q=\begin{pmatrix}
q_1&a&b\\
a&q_2&c+id\\
b&c-id&q_3
\end{pmatrix}>0,\qquad a>0,\quad b>0,
$$

where all ten parameters

$$
(p_1,p_2,p_3,q_1,q_2,q_3,a,b,c,d)
$$

are real. Their allowed set $\Omega$ is a nonempty open subset of $\mathbb R^{10}$. Strict positivity and all strict scalar inequalities are open conditions. For example, $P=\operatorname{diag}(1,2,3)$ and $Q$ with diagonal entries $4$ and all off-diagonal entries $1$ belong to this set.

We claim that distinct points of $\Omega$ give matrices $A(P,Q)$ in distinct unitary similarity classes. Indeed, since $X$ and $Y$ are invertible,

$$
\ker A=\mathbb C^3\oplus0\oplus0,
\qquad
\ker A^2=\mathbb C^3\oplus\mathbb C^3\oplus0.
$$

If $A(P',Q')=U^*A(P,Q)U$ with $U$ unitary, then $U$ preserves both of these coordinate subspaces. A unitary preserving this nested flag preserves its three orthogonal summands, so $U=\operatorname{diag}(U_1,U_2,U_3)$. The two nonzero blocks then give

$$
X'=U_1^*XU_2,\qquad Y'=U_2^*YU_3.
$$

Consequently

$$
P'=U_2^*PU_2,\qquad Q'=U_2^*QU_2.
$$

The strict ordering of the diagonal entries of $P$ and $P'$ implies $P'=P$ and $p_j'=p_j$ for each $j$. Their spectrum is simple, so $U_2$ is diagonal unitary, say $U_2=\operatorname{diag}(e^{i\theta_1},e^{i\theta_2},e^{i\theta_3})$. The $(1,2)$ and $(1,3)$ entries of $Q$ and $Q'$ are positive real numbers. The identities

$$
a'=e^{i(\theta_2-\theta_1)}a,\qquad
b'=e^{i(\theta_3-\theta_1)}b
$$

force both phases to equal one. Hence $U_2$ is scalar and $Q'=Q$. This proves the claim, including all possible unitary intertwiners of the full $9\times9$ matrices.

## 4. A positive-dimensional fiber

Let $\Phi:\Omega\to\mathbb R^9$ assign the nine non-leading coefficients of $F_{P,Q}$. Every entry of $P$ and $Q$ is linear in the ten real parameters, so $\Phi$ is a real polynomial map, in particular smooth.

Let $k$ be the maximum rank of $D\Phi$ attained on $\Omega$. This maximum exists because the nonempty set of attained ranks is a subset of $\{0,1,\ldots,9\}$. Choose $x_0\in\Omega$ at which the rank equals $k$. If $k>0$, a nonzero $k\times k$ minor stays nonzero on a neighborhood of $x_0$; the rank is at least $k$ there, and is at most $k$ by maximality. If $k=0$, the rank is already identically zero on $\Omega$. Thus in either case the derivative has constant rank $k$ on a neighborhood of $x_0$.

By the constant-rank theorem, after smooth changes of coordinates on this neighborhood and on a neighborhood of $\Phi(x_0)$, the map has the form

$$
(x_1,\ldots,x_{10})\longmapsto(x_1,\ldots,x_k,0,\ldots,0).
$$

In particular its fiber through $x_0$ contains a smooth submanifold of dimension $10-k\geq1$, and therefore contains an injective smooth curve parametrized by a nonempty open interval. All parameters on this curve lie in $\Omega$, have the same polynomial $F$, and correspond to distinct unitary classes by Section 3. Section 1 supplies equality of every singular value of every complex shift.

The positive definite square-root map is smooth, so applying $(P,Q)\mapsto A(P,Q)$ to the curve gives the smooth family asserted in the theorem. Finally $A^3=0$ and the upper-right block of $A^2$ is the invertible matrix $XY$, so its nilpotency index is three. Its kernel dimensions are $3,6,9$, and hence its Jordan type is $(3,3,3)$.

Taking arbitrarily many distinct points on this curve disproves every proposed finite bound $M_9$. This is a counterexample to the full universal statement, and does not rely on a generic-finiteness assertion.

## 5. Scope, attribution, and primary sources

The question and generic finiteness theorem are due to Maxime Fortier Bourque and Thomas Ransford. Their result outside a closed measure-zero exceptional set is compatible with this exceptional nilpotent family. The proof settles the universal finiteness question negatively; it does not claim a classification in other dimensions or an explicit numerical point on the continuous fiber.

The proof is independent of the matrix-theoretic conclusions cited below. Its only external general theorem is the standard smooth constant-rank theorem. The statement and proof explicitly supply its local constant-rank hypothesis.

- M. Fortier Bourque and T. Ransford, [*Super-identical pseudospectra*](https://doi.org/10.1112/jlms/jdn085), *Journal of the London Mathematical Society* **79**(2), 511-528 (2009), Theorem 1.4 and Section 6.2. The latter asks whether the exceptional set may be empty.
- T. Ransford, [*Pseudospectra and matrix behaviour*](https://www.impan.pl/shop/en/publication/transaction/download/product/86371), *Banach Center Publications* **91**, 327-338 (2010), Theorem 5.4 and its following discussion on printed pages 336-337. [DOI](https://doi.org/10.4064/bc91-0-19).
- G. Armentia, J. M. Gracia and F. E. Velasco, [*Identical pseudospectra of any geometric multiplicity*](https://doi.org/10.1016/j.laa.2011.01.014), *Linear Algebra and its Applications* **436**(6), 1683-1688 (2012). Their ordinary-similarity theorem is consistent with the fixed Jordan type of the family above.

The [exact diagnostic](../../references/stepaniants-sp15-2026-09-12/verification/identity-check.json) checks five determinant evaluations, including complex shifts. Those finite checks are supporting diagnostics; the proof of the full quantified identity and of the continuous fiber is the analytic argument in Sections 1-4. The [dated public eligibility check](../../references/stepaniants-sp15-2026-09-12/verification/network-check.json) and the [bounded source-search record](../../references/stepaniants-sp15-2026-09-12/verification/eligibility-and-checks.md) are separate from mathematical verification.
