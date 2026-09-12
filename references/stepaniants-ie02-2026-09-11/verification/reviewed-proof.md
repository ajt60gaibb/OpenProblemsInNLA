# IE-02: ideal and worst-case GMRES coincide for a Jordan block

Research proof candidate, 11 September 2026. Full complex target; independent
review pending. No public status or repository file has been changed.

The argument below proves a stronger statement for finite affine families of
triangular Toeplitz matrices. Its two ingredients are finite
Carathéodory–Fejér interpolation and scalar polynomial spectral factorization.
It does not require a simple maximal singular value, a divisibility hypothesis,
or a restriction on the nonzero complex eigenvalue.

## 1. Exact target and notation

**Theorem 1 (IE-02).** Let $n\ge2$, let $\lambda\in\mathbb C\setminus\{0\}$,
and let $1\le k<n$. If $J_n(\lambda)=\lambda I+N$, where
$N_{i,i+1}=1$ and all other entries are zero, and

$$
\mathcal P_k=\{p\in\mathbb C[z]:\deg p\le k,\ p(0)=1\},
$$

then

$$
\max_{\|v\|_2=1}\min_{p\in\mathcal P_k}\|p(J_n(\lambda))v\|_2
=\min_{p\in\mathcal P_k}\|p(J_n(\lambda))\|_2.
\tag{1}
$$

All vectors and polynomials are complex. We identify $\mathbb C^n$ isometrically
with

$$
\mathcal H_n=\{f\in\mathbb C[z]:\deg f\le n-1\}
\subset L^2(\mathbb T,d\theta/(2\pi)),
$$

using the coefficient basis $1,z,\ldots,z^{n-1}$. Inner products are
$\langle f,g\rangle=\int_{\mathbb T}\overline f g\,d\theta/(2\pi)$,
linear in the second argument. Write $\Pi_n$ for the orthogonal projection
onto $\mathcal H_n$. Every lower triangular Toeplitz matrix has a unique
symbol $r\in\mathcal H_n$ and acts as

$$
R f=\Pi_n(rf),\qquad f\in\mathcal H_n.
\tag{2}
$$

## 2. The maximal singular subspace of a triangular Toeplitz matrix

We use the following classical finite Carathéodory–Fejér theorem, in exactly
the form stated as **Theorem CF, §2, p. 84** of Courtney and Sarason [CS12]:
for every nonzero lower triangular Toeplitz matrix $T$ of size $n$, if
$t=\|T\|_2$, there is a finite Blaschke product $B$ of order $d\le n-1$
whose multiplication operator compresses to $T/t$ on $\mathcal H_n$.
Thus

$$
B(z)=\gamma\prod_{j=1}^{d}\frac{z-\alpha_j}{1-\overline{\alpha_j}z}
=\frac{a(z)}{b(z)},
\quad |\gamma|=1,\quad |\alpha_j|<1,
\tag{3}
$$

where

$$
a(z)=\gamma\prod_{j=1}^{d}(z-\alpha_j),\qquad
b(z)=\prod_{j=1}^{d}(1-\overline{\alpha_j}z).
$$

Empty products are allowed. In particular $\deg a=d$, $\deg b\le d$,
$a$ and $b$ are relatively prime, $b$ has no zeros on the closed unit disk,
and $|a|=|b|$ on $\mathbb T$. The theorem says

$$
Tf=t\Pi_n(Bf)\quad(f\in\mathcal H_n).
\tag{4}
$$

**Lemma 2.** The maximal right singular subspace of $T$ is

$$
E:=\ker(T^*T-t^2I)
=\{b h:\ h\in\mathbb C[z],\ \deg h\le n-1-d\}.
\tag{5}
$$

Moreover, for every such $h$,

$$
T(bh)=tah.
\tag{6}
$$

*Proof.* Multiplication by $B$ is an isometry on $L^2(\mathbb T)$, since
$|B|=1$ there. By (4) and the equality case for an orthogonal projection,

$$
\|Tf\|_2=t\|f\|_2
\quad\Longleftrightarrow\quad Bf\in\mathcal H_n.
$$

This norm equality is equivalent to $f\in E$, because
$t^2I-T^*T$ is positive semidefinite. If $Bf=g\in\mathcal H_n$, then
$af=bg$ as polynomial identities. Relative primeness gives $f=bh$ and
$g=ah$ for a polynomial $h$. Since $\deg a=d$, the condition
$g\in\mathcal H_n$ gives $\deg h\le n-1-d$ (with zero vectors included).
Conversely, that degree bound gives both $bh,ah\in\mathcal H_n$ and
$B(bh)=ah$, proving (5) and (6). $\square$

## 3. Replacing a convex combination by a single vector

We recall a scalar factorization fact and include its algebraic proof.

**Lemma 3 (polynomial spectral factorization).** For finitely many complex
polynomials $h_1,\ldots,h_s$ of degree at most $m$, and nonnegative real
numbers $\omega_1,\ldots,\omega_s$, there is a complex polynomial $h$ of
degree at most $m$ such that

$$
|h(e^{i\theta})|^2
=\sum_{\nu=1}^{s}\omega_\nu |h_\nu(e^{i\theta})|^2
\quad\text{for all real }\theta.
\tag{7}
$$

*Proof.* The right side is a nonnegative trigonometric polynomial $Q$ of
degree at most $m$. If it is zero or constant the assertion is immediate.
Otherwise let its effective degree be $\ell\le m$. The ordinary polynomial
$z^\ell Q(z)$ has degree $2\ell$, nonzero constant term, and roots paired
under $\zeta\mapsto1/\overline\zeta$. Every root on the unit circle has
even multiplicity, since the real analytic function $Q(e^{i\theta})$ is
nonnegative. Choose one root from each pair off the circle, with
multiplicity, and half of each multiplicity on the circle. The polynomial
$h_0$ with these $\ell$ roots satisfies $Q=\beta|h_0|^2$ on the circle
for a constant $\beta$. Both sides are positive at some point, so
$\beta>0$. Set $h=\sqrt\beta\,h_0$. $\square$

**Lemma 4 (simultaneous preservation).** Let $T\ne0$ be lower triangular
Toeplitz with norm $t$, and let $R_1,\ldots,R_k$ be lower triangular
Toeplitz matrices of the same size. Suppose $f_1,\ldots,f_s$ are unit vectors
in the maximal right singular subspace $E$ of $T$, and
$\omega_\nu\ge0$, $\sum_\nu\omega_\nu=1$. There is a unit vector $f\in E$
such that, simultaneously for $j=1,\ldots,k$,

$$
\langle Tf,R_j f\rangle
=\sum_{\nu=1}^{s}\omega_\nu\langle Tf_\nu,R_j f_\nu\rangle.
\tag{8}
$$

*Proof.* Write $f_\nu=b h_\nu$ as in Lemma 2, so all $h_\nu$ have degree
at most $m=n-1-d$. Apply Lemma 3 to obtain $h$ satisfying (7), and put
$f=bh$. Lemma 2 shows $f\in E$ and $Tf=tah$. Furthermore,

$$
\|f\|_2^2
=\int_{\mathbb T}|b|^2|h|^2
=\sum_\nu\omega_\nu\int_{\mathbb T}|b|^2|h_\nu|^2
=1.
\tag{9}
$$

Here and below the normalized circle measure is understood. If $r_j$ is
the symbol in (2) for $R_j$, then $ah\in\mathcal H_n$ allows the
orthogonal projection to be removed from the second argument, giving

$$
\begin{aligned}
\langle Tf,R_jf\rangle
&=t\langle ah,\Pi_n(r_j b h)\rangle\\
&=t\int_{\mathbb T}\overline a\,r_j b\,|h|^2\\
&=\sum_\nu\omega_\nu\,t\int_{\mathbb T}
  \overline a\,r_j b\,|h_\nu|^2\\
&=\sum_\nu\omega_\nu\langle Tf_\nu,R_jf_\nu\rangle.
\end{aligned}
\tag{10}
$$

This proves (8) as a complex equality, preserving both real and imaginary
parts. $\square$

## 4. The finite-dimensional optimality condition

**Lemma 5.** Suppose a nonzero matrix $T$ minimizes the operator norm on
the complex affine space $T+\operatorname{span}_{\mathbb C}
\{R_1,\ldots,R_k\}$. Put $t=\|T\|_2$ and
$E=\ker(T^*T-t^2I)$. Then finitely many unit vectors $f_\nu\in E$ and
weights $\omega_\nu\ge0$ with $\sum_\nu\omega_\nu=1$ satisfy

$$
\sum_\nu\omega_\nu\langle Tf_\nu,R_jf_\nu\rangle=0
\quad(j=1,\ldots,k).
\tag{11}
$$

*Proof.* Consider the compact set

$$
\mathcal G=
\{(\langle Tf,R_1f\rangle,\ldots,\langle Tf,R_kf\rangle):
 f\in E,\ \|f\|_2=1\}\subset\mathbb C^k\cong\mathbb R^{2k}.
$$

If zero is outside its convex hull, finite-dimensional strict separation
provides complex scalars $c_j$ and $\gamma>0$ such that, with
$D=\sum_j c_j R_j$,

$$
\operatorname{Re}\langle Tf,Df\rangle\ge\gamma
\quad(f\in E,\ \|f\|_2=1).
\tag{12}
$$

Continuity gives a neighborhood $U$ of the unit sphere of $E$ in the
full unit sphere on which the left side is at least $\gamma/2$.
On the compact complement of $U$, there is $\beta>0$ such that
$\|Tf\|_2^2\le t^2-\beta$; if the complement is empty, that part of the
argument is unnecessary. For a sufficiently small real $\varepsilon>0$,

$$
\|(T-\varepsilon D)f\|_2^2
=\|Tf\|_2^2
-2\varepsilon\operatorname{Re}\langle Tf,Df\rangle
+\varepsilon^2\|Df\|_2^2<t^2
$$

uniformly on $U$, by the $\gamma/2$ bound, and uniformly on its complement,
by the $\beta$ bound and boundedness of all other terms. This contradicts
minimality of $T$. Thus zero is in the convex hull of $\mathcal G$.
The definition of the convex hull (or Carathéodory's theorem) now gives a
finite convex combination yielding (11). $\square$

## 5. Completion of the proof

**Theorem 6 (triangular Toeplitz affine minimax).** Let $Y,R_1,\ldots,R_k$
be complex lower triangular Toeplitz matrices of the same size, and let
$\mathcal X=\operatorname{span}_{\mathbb C}\{R_1,\ldots,R_k\}$. Then

$$
\max_{\|f\|_2=1}\min_{X\in\mathcal X}\|(Y-X)f\|_2
=\min_{X\in\mathcal X}\|Y-X\|_2.
\tag{13}
$$

*Proof.* The affine matrix space $Y-\mathcal X$ is closed and finite
dimensional, so its distance to zero is attained, say at $T=Y-X_*$. If
$T=0$, both sides of (13) are zero. Otherwise apply Lemma 5 to this
minimizer, and then Lemma 4 to its convex combination. The resulting unit
vector $f$ satisfies

$$
\|Tf\|_2=\|T\|_2=t,\qquad
\langle Tf,R_jf\rangle=0\quad(j=1,\ldots,k).
\tag{14}
$$

For every $X\in\mathcal X$, the difference $X_*-X$ lies in $\mathcal X$;
hence orthogonality and the Pythagorean identity give

$$
\|(Y-X)f\|_2^2
=\|Tf+(X_*-X)f\|_2^2
=t^2+\|(X_*-X)f\|_2^2\ge t^2.
\tag{15}
$$

Taking $X=X_*$ attains equality. Thus the left side of (13) is at least
$t$, while it is at most the right side by the operator norm bound.
$\square$

*Proof of Theorem 1.* Let $W$ be the unitary reversal matrix. Then
$A=WJ_n(\lambda)W^*=\lambda I+S$, where $S$ is the lower shift. All
$I,A,A^2,\ldots,A^k$ are lower triangular Toeplitz. Apply Theorem 6 with
$Y=I$ and $\mathcal X=\operatorname{span}_{\mathbb C}\{A,\ldots,A^k\}$.
The matrices $Y-X$ are exactly $p(A)$ for $p\in\mathcal P_k$. Unitary
invariance and the bijection of unit vectors induced by $W$ give (1).
This applies directly to every allowed complex $\lambda$, without a phase
reduction. $\square$

For the stated target the minimum is strictly positive: if $p(A)=0$ and
$\deg p<n$, the independent powers $I,S,\ldots,S^{n-1}$ show that all
Taylor coefficients of $p(\lambda+z)$ vanish, forcing $p=0$ and
contradicting $p(0)=1$. The proof nevertheless already treated a zero
minimum in the more general affine theorem. It also treats constant
Blaschke products, singular residual matrices, maximal singular values of
any multiplicity, and stagnation without separate assumptions.

## 6. Status, source check, and scope

The canonical IE-02 target was read unchanged from the repository. A bounded
search on 11 September 2026 found the 2007 partial-results paper [TLF07] and
the 2025/2026 general approximation paper [FLT26], without finding a later
full resolution of the displayed target. This is a report of the searches,
not a proof of exhaustive bibliographic novelty. [FLT26] supplies related
general optimality criteria; its matrix-doubling construction is not used.
All optimality and factorization steps needed here are proved above except
the explicitly cited classical finite Carathéodory–Fejér theorem.

Earlier in this short pass, numerical coefficient diagnostics rejected a
naive Perron-Frobenius strategy requiring nonnegative optimal Toeplitz
coefficients. Those diagnostics are saved separately and are **not** a
premise or verification of Theorem 1. The present argument is analytic and
requires independent adversarial review before any solved claim.

## References

[TLF07] P. Tichý, J. Liesen, and V. Faber, *On worst-case GMRES, ideal GMRES,
and the polynomial numerical hull of a Jordan block*, Electronic
Transactions on Numerical Analysis **26** (2007), 453–473.
Author manuscript: <https://www.karlin.mff.cuni.cz/~ptichy/download/public/TiLiFa2007.pdf>.
Problem and previously established special cases; no attribution of the new
argument to that paper is intended.

[FLT26] V. Faber, J. Liesen, and P. Tichý, *Matrix best approximation in the
spectral norm*, Linear Algebra and its Applications **733** (2026),
arXiv:2506.09687. <https://arxiv.org/html/2506.09687>.
General optimality conditions and minimax background.

[CS12] D. Courtney and D. Sarason, *A mini-max problem for self-adjoint
Toeplitz matrices*, Mathematica Scandinavica **110** (2012), 82–98.
**Theorem CF, §2, p. 84**, concerning triangular Toeplitz matrices.
<https://doi.org/10.7146/math.scand.a-15198>;
publisher PDF: <https://www.mscand.dk/article/download/15198/13193/34699>.
