# MF-18: imaginary-part rank for the general complex equation

George Stepaniants  
Department of Computing and Mathematical Sciences, California Institute of Technology.  
11 September 2026.

**Research proof candidate; independent review pending.** This manuscript addresses the complete canonical complex-coefficient target. It was developed with substantial ChatGPT/Codex assistance. It does not claim external peer review, formal verification, or a result for defective unit-circle eigenvalues. No canonical page or public status has been changed by this research note.

## Theorem 1

Let $n\geq1$ and let $C,D,R,P\in\mathbb C^{n\times n}$, with $R=R^*$, $P=P^*$, and

$$
P+\lambda D^*+\lambda^{-1}D\succ0\qquad(|\lambda|=1).
$$

For every $\eta>0$, suppose $X_\eta$ is a nonsingular solution of

$$
X_\eta+(C^*+i\eta D^*)X_\eta^{-1}(C+i\eta D)=R+i\eta P
$$

such that $\rho(X_\eta^{-1}(C+i\eta D))<1$. Suppose $X_\eta$ tends to a finite nonsingular $X_0$ as $\eta\downarrow0$. Suppose the matrix polynomial

$$
\mathcal P_0(\lambda)=\lambda^2C^*-\lambda R+C
$$

is regular and all its unit-circle eigenvalues are algebraically simple. If their number is $2m$, then

$$
\boxed{\operatorname{rank}\left(\frac{X_0-X_0^*}{2i}\right)=m.}
$$

The proof permits general complex $C,D$, Hermitian $R,P$, singular $C$ or $D$, unit-circle roots at $1$ or $-1$, and arbitrary Jordan structure strictly inside the unit circle. The uniqueness assumed in the canonical statement is not needed beyond specifying the given stabilizing family.

## 1. Selecting the stable polynomial eigenvalues

Write

$$
A_\eta=C+i\eta D,\qquad B_\eta=C^*+i\eta D^*,\qquad
Q_\eta=R+i\eta P,\qquad S_\eta=X_\eta^{-1}A_\eta,
$$

and

$$
\mathcal P_\eta(\lambda)=\lambda^2B_\eta-\lambda Q_\eta+A_\eta.
$$

The finite nonsingular limit implies $S_\eta\to S=X_0^{-1}C$, so $\rho(S)\leq1$ by continuity of the roots of a characteristic polynomial. Notice that $B_\eta$ is generally different from $A_\eta^*$.

For $|\lambda|=1$, the positivity assumption at $-\lambda$ gives

$$
W(\lambda):=P-\lambda D^*-\lambda^{-1}D\succ0. \tag{1}
$$

Also $P\succ0$, since it is the average of the assumed positive matrices at $\lambda$ and $-\lambda$.

**Lemma 2.** For each $\eta>0$, the scalar polynomial $\det\mathcal P_\eta$ has exactly $n$ zeros in the open unit disk, counted with algebraic multiplicity, and none on its boundary.

**Proof.** For $t\in[0,1]$, consider

$$
\mathcal P_{\eta,t}(\lambda)
=\lambda^2(tC^*+i\eta tD^*)
 -\lambda(tR+i\eta P)+(tC+i\eta tD).
$$

On the unit circle,

$$
\lambda^{-1}\mathcal P_{\eta,t}(\lambda)
=t(\lambda C^*+\lambda^{-1}C-R)
 -i\eta\bigl[P-t(\lambda D^*+\lambda^{-1}D)\bigr].
$$

The first term is Hermitian, and the bracket is the positive-definite matrix $(1-t)P+tW(\lambda)$. The displayed matrix has negative-definite Hermitian imaginary part, hence is nonsingular. Its determinant therefore has no zero on the unit circle throughout the homotopy. The argument principle shows that the number of zeros inside is constant in $t$. At $t=0$, the polynomial is $-i\eta\lambda P$, whose determinant has exactly $n$ zeros at zero. This proves the lemma without requiring either coefficient of $\mathcal P_\eta$ to be invertible. $\square$

The nonlinear equation gives the exact factorization

$$
\mathcal P_\eta(\lambda)
=(\lambda B_\eta X_\eta^{-1}-I)X_\eta(\lambda I-S_\eta). \tag{2}
$$

Its coefficients are $B_\eta$, $-(B_\eta S_\eta+X_\eta)=-Q_\eta$, and $X_\eta S_\eta=A_\eta$. The last determinant factor already contributes $n$ zeros in the open unit disk, because $S_\eta$ is stabilizing. By Lemma 2, the polynomial

$$
\ell_\eta(\lambda)=\det(\lambda B_\eta X_\eta^{-1}-I)
$$

has no zero in that disk.

Its coefficients converge to those of

$$
\ell_0(\lambda)=\det(\lambda C^*X_0^{-1}-I),
$$

and $\ell_0(0)=(-1)^n\ne0$. Thus $\ell_0$ is not identically zero and also has no zero in the open unit disk. Indeed, if it had such a zero, choose a small circle surrounding that zero, contained in the disk, and containing no other zero on its boundary. Uniform convergence on that circle and Rouché's theorem would force $\ell_\eta$ to have a zero inside for all sufficiently small $\eta$, a contradiction.

Taking limits in (2) now gives

$$
\mathcal P_0(\lambda)
=(\lambda C^*X_0^{-1}-I)X_0(\lambda I-S). \tag{3}
$$

Consequently every eigenvalue of $\mathcal P_0$ strictly inside the unit disk is an eigenvalue of $S$, with exactly the same algebraic multiplicity there.

## 2. Counting the eigenvalues at the limit

Let $p(\lambda)=\det\mathcal P_0(\lambda)$. The coefficient symmetry gives, for $\lambda\ne0$,

$$
\mathcal P_0(\lambda)
=\lambda^2\mathcal P_0(1/\overline\lambda)^*,
\qquad
p(\lambda)=\lambda^{2n}\overline{p(1/\overline\lambda)}. \tag{4}
$$

Write $d=\deg p$ and let $z$ be its vanishing order at zero. The polynomial is nonzero by regularity. Comparing the lowest and highest nonzero coefficients in (4) gives

$$
d+z=2n. \tag{5}
$$

Each nonzero root off the unit circle is paired, with the same multiplicity, with its reciprocal conjugate. There are $2m$ unit-circle roots, so exactly half of the remaining $d-z-2m$ nonzero roots are strictly inside the disk. Including the zero root, the number of roots strictly inside is therefore

$$
z+\frac{d-z-2m}{2}=n-m. \tag{6}
$$

This argument accounts for possible singular leading coefficients: the degree $d$ need not equal $2n$.

By (3), $S$ has exactly $n-m$ eigenvalues strictly inside the unit disk, counted with multiplicity. Since its order is $n$ and $\rho(S)\leq1$, its remaining $m$ eigenvalues lie on the unit circle. They are all distinct and algebraically simple because every corresponding zero of $p$ is simple. In particular, the unit-circle part of $S$ is semisimple, and the powers $S^j$ are bounded for $j\geq0$.

## 3. A Stein identity and the missing lower bound

Set $X=X_0$ and $H=(X-X^*)/(2i)$. Taking the limit of the nonlinear equation gives

$$
X+C^*X^{-1}C=R.
$$

Since

$$
\frac{X^{-1}-X^{-*}}{2i}=-X^{-*}HX^{-1},
$$

taking Hermitian imaginary parts yields the exact Stein identity

$$
H=S^*HS. \tag{7}
$$

Let $\lambda=e^{i\theta_0}$ be one of the $m$ unit-circle eigenvalues of $S$, and let $v$ be a corresponding unit eigenvector. Then

$$
Cv=\lambda Xv. \tag{8}
$$

Consider the Hermitian matrix-valued function

$$
F(\theta)=e^{i\theta}C^*+e^{-i\theta}C-R.
$$

We have $\mathcal P_0(e^{i\theta})=e^{i\theta}F(\theta)$. Thus the simple determinant root of $\mathcal P_0$ at $\lambda$ gives a simple zero of $\det F(\theta)$ at $\theta_0$. It follows that $F(\theta_0)$ has one-dimensional kernel spanned by $v$, and

$$
a:=v^*F'(\theta_0)v
=v^*(i\lambda C^*-i\lambda^{-1}C)v\ne0. \tag{9}
$$

For completeness, a simple determinant zero forces nullity one because a matrix with nullity at least two has zero adjugate and therefore zero determinant derivative. For the Hermitian matrix $F(\theta_0)$ with one-dimensional kernel, its adjugate is $\kappa vv^*$ for a nonzero real $\kappa$. The determinant derivative is consequently $\kappa v^*F'(\theta_0)v$, proving (9), including when $n=1$.

Equation (8) and $|\lambda|=1$ give the direct identity

$$
a=i\bigl(v^*X^*v-v^*Xv\bigr)=2v^*Hv. \tag{10}
$$

Hence $v^*Hv\ne0$ at each of the selected unit-circle eigenvectors. If $v_j,v_k$ correspond to distinct unit-circle eigenvalues $\lambda_j,\lambda_k$, (7) gives

$$
(1-\overline{\lambda_j}\lambda_k)v_j^*Hv_k=0.
$$

The scalar prefactor is nonzero for $j\ne k$, so all these cross terms vanish. The Gram matrix of $H$ on the span of the $m$ unit-circle eigenvectors is diagonal with nonzero diagonal entries, by (10). It is nonsingular, and therefore

$$
\operatorname{rank}H\geq m. \tag{11}
$$

## 4. The stable generalized eigenspace gives the upper bound

Let $E_s$ be the generalized eigenspace of $S$ corresponding to its eigenvalues strictly inside the unit disk. Its dimension is $n-m$, and $S^j x\to0$ for every $x\in E_s$. Iterating (7) gives, for any $y\in\mathbb C^n$,

$$
x^*Hy=(S^j x)^*H S^j y.
$$

The right-hand side tends to zero because $S^j x\to0$ and the powers of $S$ are bounded. Hence $x^*H=0$. Since $H$ is Hermitian, $Hx=0$, and $E_s\subseteq\ker H$. Consequently

$$
\operatorname{rank}H\leq m. \tag{12}
$$

Together, (11) and (12) prove Theorem 1. If $m=0$, the stable-subspace argument directly gives $H=0$. No differentiability of the family $X_\eta$, positivity of $H$, or diagonalizability of the stable part was used. $\square$

## Scope, attribution, and status

Guo, Kuo, and Lin prove the upper bound and formulate the equality conjecture in their 2012 JCAM paper. Their earlier SIMAX paper addresses the real-coefficient scalar-regularization setting. Matthew J. Colbrook's existing repository contribution proves an auxiliary real-coefficient theorem that also treats defective unit-circle structure. That contribution remains credited and is not a premise of the present general-complex proof. The argument here retains the canonical simple-eigenvalue hypothesis and does not claim the defective extension.

The parent agent's public-network audit on 11 September 2026 checked all five available repositories and 28 branch heads and found no posted full resolution of the general complex target; the existing MF-18 contribution was still partial. A bounded primary-source literature check likewise found the conjecture, the known upper bound, and the prior real subcase. This is a status check, not a proof of historical priority. Independent review of this exact manuscript is pending.

## References

1. [MF-18 canonical problem statement](https://github.com/MColbrook/OpenProblemsInNLA/blob/main/matrix-functions-and-stability/MF-18/README.md).
2. C.-H. Guo, Y.-C. Kuo, W.-W. Lin, [*Numerical solution of nonlinear matrix equations arising from Green's function calculations in nano research*](https://doi.org/10.1016/j.cam.2012.05.012), Journal of Computational and Applied Mathematics 236 (2012), 4166–4180; Theorem 5 and the conjecture on p. 4172. [Author manuscript](https://uregina.ca/~chguo/JCAM_GuoKuoLin.pdf).
3. C.-H. Guo, Y.-C. Kuo, W.-W. Lin, [*On a nonlinear matrix equation arising in nano research*](https://doi.org/10.1137/100814706), SIAM Journal on Matrix Analysis and Applications 33 (2012), 235–262, Section 3. [Author manuscript](https://uregina.ca/~chguo/simax81470.pdf).
4. Matthew J. Colbrook, [existing MF-18 auxiliary manuscript](https://github.com/MColbrook/OpenProblemsInNLA/blob/main/references/colbrook-matrix-functions-2026-09-11/manuscripts/MF-18.tex), Theorem 1, Corollary 3, and Section 8, with the repository's stated real-coefficient scope and independent-agent review.
