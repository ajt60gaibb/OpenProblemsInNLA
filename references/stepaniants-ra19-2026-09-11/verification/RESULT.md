# RA-19: an eliminant proof of the one-zero corank-one ED-degree formula

**Status:** complete proof candidate, pending an independent mathematical review. This private research note makes no publication, external peer-review, formal-certification, or priority claim.

**Target and attribution.** Kubjas, Sodomaco and Tsigaridas, *Exact solutions in low-rank approximation with zeros*, LAA 641 (2022), Conjecture 5.1 and Table 2, manuscript page 19, propose the formula below. The current arXiv record remains version 2 (29 January 2022). The exact canonical target is preserved in `canonical-target.md`. The dimension-two exception is excluded by that target and is explained below.

All transposes and inner products are bilinear over the complex numbers; no complex conjugation is used.

## 1. Theorem and notation

**Theorem.** For every integer $n\ge3$, let

$$V_n=\{X\in\mathbb C^{n\times n}:\det X=0,\ x_{11}=0\}.$$

Then its Euclidean distance degree for the bilinear squared Frobenius distance is

$$\operatorname{EDdeg}(V_n)=5n-7.$$

Put $m=n-1\ge2$. The entry $u_{11}$ contributes a constant to the objective on $V_n$. Write the other data in the form

$$A(z)=\begin{pmatrix}z&b^T\\c&D\end{pmatrix},\qquad b,c\in\mathbb C^m.$$

For generic data, orthogonal transformations on the last $m$ rows and columns put $D$ in the form $\operatorname{diag}(d_1,\ldots,d_m)$, with nonzero, distinct squared entries. These transformations preserve the metric and the fixed-zero constraint. To see the generic reduction, diagonalize $DD^T$ in an orthonormal eigenbasis and obtain the right orthogonal factor by applying $D^T$ and dividing by the nonzero singular values. Distinct eigenvalues of a complex symmetric matrix have orthogonal eigenvectors, and a simple eigenvalue has a nonisotropic eigenvector. Thus the reduction applies on a nonempty algebraic open set. The parameters $b,c$ remain unrestricted there.

Let $\lambda$ denote a squared singular-value parameter, and define

$$f(\lambda)=\prod_{i=1}^m(\lambda-d_i^2),\quad
f_i(\lambda)=\frac{f(\lambda)}{\lambda-d_i^2},$$

$$F_b=f-\sum_i b_i^2f_i,\qquad
F_c=f-\sum_i c_i^2f_i,\qquad
g=\sum_i d_i b_i c_i f_i.$$

The letter $E$ below denotes a scalar polynomial, while $E_{11}$ denotes the matrix unit.

## 2. A quadratic spectral curve

**Lemma 1.** There is a monic polynomial $h$ of degree $m+1$ such that

$$P(\lambda,z):=\det(\lambda I-A(z)A(z)^T)
=h(\lambda)-2g(\lambda)z-f(\lambda)z^2,\tag{1}$$

and

$$f h+g^2=\lambda F_bF_c.\tag{2}$$

**Proof.** Away from $f=0$, eliminate the bottom coordinates in the eigenvalue equations for the symmetric matrix

$$\begin{pmatrix}0&A(z)\\A(z)^T&0\end{pmatrix}.$$

Writing $t^2=\lambda$, the remaining $2\times2$ determinant is

$$\lambda\left(1-\sum_i\frac{b_i^2}{\lambda-d_i^2}\right)
\left(1-\sum_i\frac{c_i^2}{\lambda-d_i^2}\right)
-\left(z+\sum_i\frac{d_i b_i c_i}{\lambda-d_i^2}\right)^2.$$

Multiplication by $f$ gives the characteristic polynomial (1), first on the open set where the elimination is legal and then identically. Equivalently, this follows by a Schur complement, with its leading coefficient fixed by the monic characteristic polynomial. The double poles cancel: their coefficient at $\lambda=d_i^2$ is proportional to $\lambda-d_i^2$. Hence $h=(\lambda F_bF_c-g^2)/f$ is a polynomial. Its leading term is $\lambda^{m+1}$. This also proves (2). $\square$

The plane curve $P=0$ therefore has the completed-square equation

$$fP=\lambda F_bF_c-(fz+g)^2.\tag{3}$$

We shall use the following generic conditions, all verified simultaneously in Section 5:

1. $f$ has simple nonzero roots, $g$ is nonzero at those roots, and its leading coefficient $G=\sum_i d_i b_i c_i$ is nonzero.
2. $\lambda F_bF_c$ is squarefree, and $g(0)\ne0$.
3. $g$ and $h$ have no common root.
4. The two polynomials $P$ and

   $$E(\lambda,z):=\tfrac12P_z+zP_\lambda
   =-g+(h'-f)z-2g'z^2-f'z^3\tag{4}$$

   have no common zero with $f(\lambda)=0$ or with $z=z_*:=c^TD^{-1}b$.
5. The one-dimensional left and right kernels of $A(z_*)$ are nonisotropic. Both $b$ and $c$ are nonzero, and $z_*\ne0$.

These are nonvanishing conditions on finitely many polynomial or rational expressions in the parameters. Resultants express the assertions of no common root. Clearing the nonzero denominators gives algebraic open conditions.

Under conditions 1–2 the affine curve $P=0$ is smooth. When $f\ne0$, use the invertible coordinate $w=fz+g$ and (3): $w^2=\lambda F_bF_c$ has no singular point because its right side is squarefree. When $f=0$, the partial derivative $P_z=-2g$ is nonzero.

## 3. Exact correspondence with distance critical points

**Lemma 2.** Under the generic conditions above, the solutions of $P=E=0$ are in bijection with the critical points of the distance function on the smooth locus of $V_n$.

**Proof.** The restriction of the determinant to $x_{11}=0$ is a nonzero, squarefree polynomial: it is of degree at most one in every individual remaining entry, which prevents any nonconstant repeated factor. The Jacobian criterion for a reduced hypersurface therefore implies that a smooth point has rank $n-1$, and that its determinant gradient is not proportional to $E_{11}$. In particular, rank at most $n-2$ cannot be smooth.

Let $X$ be a smooth distance-critical point, and let nonzero $u,v$ span its left and right kernels. Its normal space is spanned by $E_{11}$ and $uv^T$. Thus for some scalars $t,s$,

$$U-X=tE_{11}+suv^T.$$

Set $z=u_{11}-t$, so $A(z)-X=suv^T$. If $s=0$, then $A(z)=X$ and $x_{11}=0$ force $z=0$, contradicting the generic invertibility of $A(0)$; indeed $D$ is invertible and $z_*\ne0$.

Neither $u$ nor $v$ is isotropic. For example, if $u^Tu=0$, then $A(z)^Tu=0$. Since $\det A(z)=\det D\,(z-z_*)$, this forces $z=z_*$, and $u$ is the left kernel vector of $A(z_*)$, contrary to condition 5. The argument for $v$ is identical. We may therefore normalize $u^Tu=v^Tv=1$, absorbing the scaling into $s$. Then

$$A(z)v=su,\qquad A(z)^Tu=sv,\qquad
A(z)A(z)^Tu=\lambda u,\quad \lambda=s^2\ne0.\tag{5}$$

The eigenvalue $\lambda$ is simple. If it were not, the nonisotropic eigenvector $u$ splits off as an orthogonal invariant one-dimensional summand. The complementary summand must also have eigenvalue $\lambda$, so the geometric eigenspace has dimension at least two. Consequently the adjugate of $\lambda I-A(z)A(z)^T$ vanishes, giving $P_\lambda=P_z=0$ at $P=0$, contrary to the smoothness of the plane spectral curve.

Let $\Pi$ be the orthogonal spectral projector for this simple eigenvalue. Then $\Pi=uu^T$ and

$$A(z)-X=\Pi A(z).\tag{6}$$

Differentiating the simple eigenvalue in the $z$ direction gives

$$\lambda'(z)=u^T(E_{11}A(z)^T+A(z)E_{11})u
=2(\Pi A(z))_{11}.\tag{7}$$

Since $X_{11}=0$, equations (6)–(7) give $\lambda'=2z$. Implicit differentiation of $P(\lambda(z),z)=0$ is now legitimate and gives $E=0$.

Conversely, suppose $P=E=0$. Condition 4 excludes $f=0$ and $z=z_*$. Smoothness of $P=0$ and equation (4) imply $P_\lambda\ne0$, since otherwise also $P_z=0$. Moreover $\lambda\ne0$: at $\lambda=0$, identity (2) makes the unique $z$ root equal to $-g(0)/f(0)\ne0$, with $P_z=0$; smoothness gives $P_\lambda\ne0$, and hence $E=zP_\lambda\ne0$.

Thus $A(z)$ is invertible and $\lambda$ is simple and nonzero. Its spectral projector is

$$\Pi=\frac{\operatorname{adj}(\lambda I-A(z)A(z)^T)}{P_\lambda(\lambda,z)}.$$

Define $X=A(z)-\Pi A(z)$. This matrix has rank $n-1$. Equation (7), together with $E=0$, gives $X_{11}=0$. If its determinant gradient were proportional to $E_{11}$, its left and right kernels would both be spanned by $e_1$, forcing $\Pi A(z)$ to be proportional to $E_{11}$ and hence the off-diagonal part $b^T$ of the first row of $A(z)$ to vanish. This contradicts condition 5. Therefore $X$ is smooth on $V_n$.

The matrix $\Pi A(z)$ is a rank-one normal to the rank-$n-1$ determinantal hypersurface at $X$: its row and column directions are the right and left kernels of $X$. Adding $(u_{11}-z)E_{11}$ gives $U-X$, so $X$ is distance critical. The two constructions are inverse. In particular the projector formula gives only one $X$ for each pair $(\lambda,z)$; the choice of square root of $\lambda$ introduces no doubling. $\square$

## 4. Degree of the stationarity eliminant

Set

$$\begin{aligned}
\alpha&=f^2(h'-f)+4fgg'-ff'h-4f'g^2,\\
\beta&=-f^2g-2fg'h+2f'gh.
\end{aligned}\tag{8}$$

Reducing the cubic (4) modulo $P$ gives

$$E\equiv\frac{\alpha z+\beta}{f^2}\pmod P.\tag{9}$$

The resultant in $z$ is consequently

$$R(\lambda):=\operatorname{Res}_z(P,E)
=\frac{h\alpha^2+2g\alpha\beta-f\beta^2}{f^2}.\tag{10}$$

For completeness, the degree-two leading coefficient of $P$ is $-f$. In replacing the degree-three second polynomial by its degree-one remainder, the resultant gains the factor $(-f)^2$. The two appearances of the denominator $f^2$ contribute $f^{-4}$. The resultant with the numerator $\alpha z+\beta$ is $\alpha^2P(\lambda,-\beta/\alpha)$. This proves (10) as a rational identity, and hence as the polynomial identity obtained by taking the original Sylvester resultant. In particular the numerator is divisible by $f^2$; it is not necessary to discard those factors by an informal saturation.

Write $h=\lambda f+r$, with $\deg r\le m$. Then

$$\alpha=f(fr'-f'r)+4g(fg'-f'g).$$

The top-degree terms of $fr'-f'r$ cancel, so $\deg\alpha\le3m-2$. Since $g=G\lambda^{m-1}+\cdots$ with $G\ne0$,

$$fg'-f'g=-G\lambda^{2m-2}+\cdots,\qquad
\beta=G\lambda^{3m-1}+\cdots.$$

In the numerator of (10), the term $-f\beta^2$ has degree $7m-2$ and leading coefficient $-G^2$. The other terms have degree at most $7m-3$ and $7m-4$, respectively. Dividing by the monic $f^2$ yields

$$\deg R=5m-2=5n-7.\tag{11}$$

Under the generic conditions, every root of $R$ comes from a finite common zero of $P,E$. At a root of $f$, the projectivized quadratic $P$ vanishes at $z=\infty$, but the cubic $E$ has leading coefficient $-f'\ne0$ there; hence there is no common point at infinity. Condition 4 also excludes a common finite point over those roots. At all other $\lambda$, $P$ has its nonzero quadratic leading coefficient and the usual resultant criterion applies. No root at $\lambda=0$ is automatic: the additional term $zP_\lambda$ in (4) excludes it, as established in Lemma 2.

It remains to justify that the degree counts critical points rather than repeated scheme length. We include this standard genericity step explicitly.

**Lemma 3 (generic reducedness and resultant counting).** For generic data satisfying the preceding open conditions, the number of common zeros of $P,E$ is $\deg R$, counting distinct pairs, and these are the distinct distance-critical points.

**Proof.** The Euclidean critical correspondence over the smooth locus of a variety is its translated normal bundle:

$$\mathcal C=\{(X,U):X\in V_n^{\rm sm},\ U-X\in (T_XV_n)^\perp\}.$$

It is smooth of dimension $n^2$, since the normal fibers have dimension two. The nonzero resultant and Lemma 2 show that its generic projection to the $n^2$ data coordinates has finite fibers. Dominating components therefore give finite extensions of the rational function field of the data. In characteristic zero these extensions are separable; after removing the discriminants and denominators, their finite fibers are reduced. Nondominating components are avoided by removing their proper images. This proves generic reducedness without assuming a numerical critical-point count.

Here reducedness also applies to the particular equations $P=E=0$, not only to their set of points. On the good open set, the ordinary corank-one critical correspondence is locally the simple spectral cover of $A$: its inverse is the regular projector formula (6), while the forward map recovers $\lambda$ from the rank-one residual. Adding the constraint $X_{11}=0$ cuts that correspondence by a smooth hypersurface whenever $X$ is smooth on $V_n$. Indeed the ordinary correspondence projects smoothly to the rank-$n-1$ matrix $X$, and $x_{11}=0$ is transverse there precisely when the determinant gradient and $E_{11}$ are independent. In the spectral coordinates this exact constraint is

$$X_{11}=z-\frac{\lambda'(z)}2=\frac{E}{P_\lambda}.$$

Thus, with the nonzero factor $P_\lambda$ removed, the local constrained correspondence has exactly the equations $P=E=0$, with their reduced local structure. The free data coordinate $u_{11}$ only adds an affine factor. The generic fibers of this equation system are therefore reduced as well.

Finally, no common point has $z=0$: such a point would satisfy $g=h=0$, excluded by condition 3. Hence (4) gives $P_z=-2zP_\lambda\ne0$ at every common point. Locally the two roots of the quadratic in $z$ are distinct analytic functions of $\lambda$. The product formula for the resultant is a nonzero factor times the product of $E$ along these two branches. Its root multiplicity is therefore the sum of the local intersection multiplicities, each equal to one by the preceding reducedness. This remains true if two distinct pairs share the same value of $\lambda$. Summing multiplicities of the univariate resultant gives the number of distinct pairs, namely $\deg R$. $\square$

## 5. A simultaneous witness for every required generic condition

Fix $0<d_1<\cdots<d_m$, fix $\beta_i>0$, and choose a real $r>0$ with $r\ne1$. Set

$$D=\operatorname{diag}(d_i),\qquad b=\epsilon\beta,\qquad c=r\epsilon\beta,$$

where $\epsilon>0$ is sufficiently small. In this section only, $\beta_i$ denotes the fixed vector entries, not the polynomial $\beta$ in (8).

The polynomials $F_b,F_c$ are the characteristic polynomials of $D^2+\epsilon^2\beta\beta^T$ and $D^2+r^2\epsilon^2\beta\beta^T$. Each has distinct positive roots: its secular function has strictly positive derivative between its poles, one root between each pair of successive $d_i^2$, and one root beyond the largest pole. These two root sets are disjoint. A common root away from $f=0$ would make both $1-\epsilon^2\sum_i\beta_i^2/(\lambda-d_i^2)$ and $1-r^2\epsilon^2\sum_i\beta_i^2/(\lambda-d_i^2)$ zero, forcing $r^2=1$; at a pole neither characteristic polynomial vanishes. Thus $\lambda F_bF_c$ is squarefree. Also $G=r\epsilon^2\sum_i d_i\beta_i^2\ne0$, and $g$ is nonzero at every root of $f$ and at zero.

The zeros of $g/\epsilon^2$ are fixed as $\epsilon$ varies. They lie strictly between successive poles $d_i^2$, since its secular sum has positive weights $d_i\beta_i^2$. None is zero or a pole. The roots of $h=P(\lambda,0)$ tend to $0,d_1^2,\ldots,d_m^2$ as $\epsilon\to0$. Consequently $g,h$ have no common root for sufficiently small positive $\epsilon$.

At $\lambda=d_i^2$, let $q_i=f'(d_i^2)\ne0$. Direct expansion of the polynomials gives

$$g(d_i^2)=r\epsilon^2d_i\beta_i^2q_i,$$

$$h(d_i^2)=-(1+r^2)\epsilon^2d_i^2\beta_i^2q_i+O(\epsilon^4).$$

The unique finite root of $P(d_i^2,z)$ therefore satisfies

$$z_i=-\frac{(1+r^2)d_i}{2r}+O(\epsilon^2).$$

As $\epsilon\to0$, $h'(d_i^2)\to d_i^2q_i$ and $g,g'\to0$. It follows that

$$E(d_i^2,z_i)\longrightarrow q_i z_i^{(0)}\bigl(d_i^2-(z_i^{(0)})^2\bigr)\ne0,$$

because $z_i^{(0)}=-(1+r^2)d_i/(2r)$ is nonzero and has absolute value strictly greater than $d_i$. This excludes every common finite point above a root of $f$.

It remains to exclude the singular completion. It occurs exactly at

$$z_*=r\epsilon^2\sum_j\frac{\beta_j^2}{d_j}>0.$$

The matrix $A(z_*)$ has rank $m$, and its left and right kernel vectors can be chosen as $(1,-\epsilon D^{-1}\beta)^T$ and $(1,-r\epsilon D^{-1}\beta)^T$. Their bilinear squared norms are positive, so they are nonisotropic. The zero squared singular value is simple and cannot satisfy $E=0$, since $P_z=0$ there and $z_*P_\lambda\ne0$.

For each of the $m$ nonzero squared singular values near $d_i^2$, choose its real normalized left singular vector $u_i$ with its $i$-th lower coordinate positive. Ordinary simple-eigenvalue perturbation, or substitution into its eigenvector equation, gives

$$ (u_i)_1=\epsilon\frac{\beta_i}{d_i}+O(\epsilon^3),\qquad
(A(z_*)^Tu_i)_1=r\epsilon\beta_i+O(\epsilon^3).$$

These expansions follow directly from the top-to-$i$ entry $\epsilon d_i\beta_i+O(\epsilon^3)$ of $A(z_*)A(z_*)^T$, with limiting eigenvalue $d_i^2$. Odd/even parity under $\epsilon\mapsto-\epsilon$ gives the stated remainder orders. Therefore the rank-one spectral residual satisfies

$$ (\Pi_i A(z_*))_{11}=r\epsilon^2\frac{\beta_i^2}{d_i}+O(\epsilon^4),$$

and its putative fixed-zero approximation has

$$\bigl(A(z_*)-\Pi_i A(z_*)\bigr)_{11}
=r\epsilon^2\sum_{j\ne i}\frac{\beta_j^2}{d_j}+O(\epsilon^4)>0\tag{12}$$

for sufficiently small $\epsilon$, because $m\ge2$. By (7), none of these eigenvalues satisfies $E=0$. This proves the remaining exclusion in condition 4. All listed conditions thus hold simultaneously for sufficiently small positive $\epsilon$.

Since every failure condition is algebraic, this real family proves that the needed complex algebraic open set is nonempty in every dimension $m\ge2$. Lemmas 1–3 and (11) prove the theorem.

## 6. The exceptional dimension two and scope

When $m=1$, the sum in (12) is empty. At the singular completion, subtracting the only nonzero singular component gives $X=0$, which is singular on the union defined by $x_{12}x_{21}=0$. That extraneous point explains why the degree-three stationarity eliminant does not equal the dimension-two ED degree, which is two. It is not a zero-eigenvalue artifact. The proof above uses $m\ge2$ precisely to remove this singular-completion phenomenon.

The result counts complex smooth-locus critical points for generic complex data, with the original bilinear distance and the single fixed entry. It makes no assertion that all critical points are real, that a particular numerical algorithm finds them, or that the more general zero-pattern conjectures are resolved.

## 7. Primary source and bounded status check

- Kubjas–Sodomaco–Tsigaridas, [arXiv:2010.15636v2](https://arxiv.org/abs/2010.15636v2), [PDF](https://arxiv.org/pdf/2010.15636v2), Conjecture 5.1 and Table 2, page 19; published [DOI 10.1016/j.laa.2022.01.021](https://doi.org/10.1016/j.laa.2022.01.021). The downloaded primary PDF and extracted page 19 are preserved privately alongside this note. The formula there is $5(n-1)-2$, identical to the canonical $5n-7$.
- The current arXiv record still lists version 2, dated 29 January 2022. Exact-title, conjecture-number, one-zero and ED-degree searches found no later full proof. The source's reported orders 3–10 are finite evidence, not a premise of this argument.
- The public RA-19 PR search returned only merged admission PR 111, which lists RA-19 as open and resolves a different RA-20 target. A full current public-branch eligibility snapshot is a separate pending check before any potential publication.

This manuscript is a new private proof candidate prepared with AI assistance. It requires an independent adversarial review of the generic correspondence, reducedness argument and all exceptional-locus exclusions before any solved status or submission.
