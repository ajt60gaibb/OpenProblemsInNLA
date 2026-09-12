---
title: "MF-22: An eventual linear condition-number bound"
author: George Stepaniants
affiliation: Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA.
date: 11 September 2026
review-footer: "AI-assisted proof; independent automated-agent review documented in the submission record."
---

\pagestyle{plain}
\setlength{\abovedisplayskip}{6pt}
\setlength{\belowdisplayskip}{6pt}
\setlength{\abovedisplayshortskip}{4pt}
\setlength{\belowdisplayshortskip}{4pt}

This manuscript proves an eventual linear condition-number bound for the exact cubic $C^1$ spline Schrödinger Toeplitz family in MF-22. It was developed with substantial ChatGPT/Codex assistance at the author's request. A separate [independent Codex-agent review](../../references/stepaniants-mf22-2026-09-11/verification/MF-22-independent-review.md) returned PASS for the complete target. This is automated-agent review, not external human peer review or formal proof-assistant verification.

## 1. Statement and exact transfer recurrence

**Theorem.** For every fixed real $\rho>0$, the matrices $H_n(\rho)$ in MF-22 are nonsingular for every sufficiently large $n$, and

\nopagebreak[4]

$$
\kappa_2(H_n(\rho))\le K_\rho n
$$

for all sufficiently large $n$, with a finite constant $K_\rho$ independent of $n$.

Write $r=\rho$ and $M_n=80H_n$. Introduce the fixed complex numbers

\nopagebreak[4]

$$
\begin{aligned}
A&=-r-6i,& B&=-7r-30i,& C&=7r-30i,\\
D&=-25r-30i,& E&=r-6i,& F&=25r-30i.
\end{aligned}
$$

These letters denote scalars, not the original coefficient blocks. Writing the unknown vector as $(u_0,v_0,\ldots,u_{n-1},v_{n-1})^T$, the two equations in block row $j$ of $M_nx=f$ are exactly

\nopagebreak[4]

$$
\begin{aligned}
A u_{j+1}-24r u_j+F u_{j-1}
 +Bv_j+96iv_{j-1}+Cv_{j-2}&=f_{j,1},\\
B u_{j+1}+96iu_j+C u_{j-1}
 +Dv_j+24rv_{j-1}+Ev_{j-2}&=f_{j,2},
\end{aligned}
\tag{1}
$$

for $0\le j<n$, with the boundary convention

\nopagebreak[4]

$$
u_{-1}=v_{-1}=v_{-2}=0,\qquad u_n=0.
\tag{2}
$$

There is no boundary condition on $v_n$: this variable does not occur in (1). Set

\nopagebreak[4]

$$
a=30-r^2-10ir,\qquad
L=\begin{pmatrix}A&B\\B&D\end{pmatrix}.
$$

Since $\det L=24a$ and $r>0$, $L$ is invertible. Define

\nopagebreak[4]

$$
T=\begin{pmatrix}
\multicolumn{4}{c}{L^{-1}\begin{pmatrix}24r&-96i&-F&-C\\-96i&-24r&-C&-E\end{pmatrix}}\\
1&0&0&0\\
0&1&0&0
\end{pmatrix},
\qquad
G=\begin{pmatrix}L^{-1}\\0_{2\times2}\end{pmatrix}.
\tag{3}
$$

\Needspace{10\baselineskip}

The top two rows in (3) are the displayed $2\times4$ product. If

\nopagebreak[4]

$$
w_j=(u_j,v_{j-1},u_{j-1},v_{j-2})^T,
\qquad e=(1,0,0,0)^T,
$$

then (1) and (2) become precisely

\nopagebreak[4]

$$
w_{j+1}=Tw_j+Gf_j,\qquad w_0=e u_0,\qquad e^T w_n=0,
\tag{4}
$$

where $f_j=(f_{j,1},f_{j,2})^T$. All constants and matrices in (3) are independent of $n$.

## 2. A scalar generating function and absence of cancellation

Consider the homogeneous forward recurrence (4), without imposing its right boundary, with $u_0=1$. Thus $w_j=T^je$. Its formal generating functions

\nopagebreak[4]

$$
U(z)=\sum_{j\ge0}u_jz^j,\qquad V(z)=\sum_{j\ge0}v_jz^j
$$

satisfy, by summing (1),

\nopagebreak[4]

$$
\begin{pmatrix}\alpha(z)&z h(z)\\h(z)&z\ell(z)\end{pmatrix}
\begin{pmatrix}U(z)\\V(z)\end{pmatrix}
=\begin{pmatrix}A\\B\end{pmatrix},
\tag{5}
$$

where

\nopagebreak[4]

$$
\alpha(z)=A-24rz+Fz^2,\quad
h(z)=B+96iz+Cz^2,\quad
\ell(z)=D+24rz+Ez^2.
$$

Consequently

\nopagebreak[4]

$$
U(z)=\frac{A\ell(z)-Bh(z)}{\alpha(z)\ell(z)-h(z)^2}
     =\frac{N(z)}{d(z)},
\tag{6}
$$

where direct multiplication gives

\nopagebreak[4]

$$
\begin{aligned}
N(z)&=a+(-120-r^2+22ir)z+2(r^2+18)z^2,\\
d(z)&=a+bz+cz^2+\overline b z^3+\overline a z^4,\\
b&=24r^2+80ir-240,\qquad c=420-46r^2.
\end{aligned}
\tag{7}
$$

Both numerator and denominator in the middle expression of (6) are $24$ times the corresponding polynomial in (7). In particular, $d(0)=a\ne0$.

**Lemma 1.** For every $r>0$, the polynomials $N$ and $d$ have no common complex root.

**Proof.** Suppose $z$ were a common root. The middle expression in (6) yields

\nopagebreak[4]

$$
A\ell(z)=Bh(z),\qquad
\alpha(z)\ell(z)=h(z)^2.
$$

Since $A\ne0$, either $h(z)=\ell(z)=0$, or

\nopagebreak[4]

$$
Ah(z)=B\alpha(z).
\tag{8}
$$

The first possibility is excluded by the following exact resultant calculation:

\nopagebreak[4]

$$
\operatorname{Res}_z(h,\ell)
=2177280+946944r^2+i(622080r+241920r^3).
\tag{9}
$$

\Needspace{6\baselineskip}

Its real part is positive. For completeness, (9) follows by inserting the coefficients in the quadratic resultant identity

\nopagebreak[4]

$$
\operatorname{Res}(a_2z^2+a_1z+a_0,b_2z^2+b_1z+b_0)
=(a_2b_0-a_0b_2)^2
 -(a_2b_1-a_1b_2)(a_1b_0-a_0b_1).
$$

In the second possibility, direct subtraction gives

\nopagebreak[4]

$$
Ah(z)-B\alpha(z)
=24z\bigl[24-7r^2-34ir+(7r^2+30+22ir)z\bigr].
$$

\Needspace{7\baselineskip}

The root $z=0$ is unavailable because $d(0)\ne0$. The denominator in the following expression has positive real part, so (8) forces

\nopagebreak[4]

$$
z=z_0:=\frac{7r^2-24+34ir}{7r^2+30+22ir}.
$$

Set $y=r^2$. Substitution into $N$ gives exactly

\nopagebreak[4]

$$
(7r^2+30+22ir)^2N(z_0)=R(y)+irI(y),
\tag{10}
$$

where

\nopagebreak[4]

$$
\begin{aligned}
R(y)&=134136+32436y-10404y^2,\\
I(y)&=-103032-40632y+840y^2.
\end{aligned}
$$

Because $r>0$, a zero in (10) would imply $R(y)=I(y)=0$. This is impossible, since

\nopagebreak[4]

$$
70R(y)+867I(y)=-79939224-32957424y<0
\qquad(y\ge0).
\tag{11}
$$

Both alternatives are excluded. $\square$

## 3. The four characteristic roots, including the exceptional parameter

Let

\nopagebreak[4]

$$
p(t)=t^4d(1/t)
=at^4+bt^3+ct^2+\overline b t+\overline a.
\tag{12}
$$

This is also the quartic in the source's Proposition 5.14, up to its stated nonzero determinant factor. We give the root classification explicitly so that no exceptional positive parameter is suppressed.

Since $p(1)=0$, write

\nopagebreak[4]

$$
p(t)=(t-1)q(t),\qquad
q(t)=at^3+(a+b)t^2-(\overline a+\overline b)t-\overline a.
$$

Here $q(1)=120ir\ne0$. Under the Cayley substitution,

\nopagebreak[4]

$$
(1-ix)^3q\!\left(\frac{1+ix}{1-ix}\right)=8i\mathcal R_r(x),
\tag{13}
$$

where

\nopagebreak[4]

$$
\mathcal R_r(x)=6(r^2-10)x^3+25rx^2+5(r^2-6)x+15r.
$$

\Needspace{5\baselineskip}

The cubic discriminant expression is

\nopagebreak[4]

$$
\begin{aligned}
\Delta_r
&=-25r^4(120r^4-3337r^2+34200)
  -5269500r^2-6480000<0.
\end{aligned}
\tag{14}
$$

Indeed the quadratic $120y^2-3337y+34200$ is positive for every real $y$, since its leading coefficient is positive and its discriminant is $-5280431$.

If $r\ne\sqrt{10}$, the polynomial $\mathcal R_r$ is cubic. Its negative discriminant means that it has one real root and two distinct nonreal conjugate roots. The Cayley map sends the real root to the unit circle, and sends the conjugate nonreal pair to a pair related by reciprocal conjugation, one strictly inside and one strictly outside the circle. Its inverse pole $x=-i$ is not a root in (13): direct substitution gives $\mathcal R_r(-i)=-ia\ne0$. Thus all three roots correspond to finite nonzero roots of $q$. Also $t=-1$ is not a root in this case, because $q(-1)=48(r^2-10)\ne0$.

\Needspace{10\baselineskip}

If $r=\sqrt{10}$, then

\nopagebreak[4]

$$
\mathcal R_r(x)=25rx^2+20x+15r
$$

has discriminant $400-1500r^2=-14600<0$. Its two roots form a nonreal conjugate pair. The missing third Cayley root is $t=-1$, which is a simple root of $q$: the quadratic term $25rx^2$ is nonzero, so the homogeneous cubic in (13) has a simple root at infinity. Equivalently, direct differentiation gives $q'(-1)=-100ir\ne0$. Again there is one root strictly inside and one strictly outside the circle, together with the simple unit root $-1$.

Therefore, for every $r>0$, $p$ has four distinct nonzero roots: two on the unit circle (one equal to $1$), one strictly inside, and one strictly outside. Denote the outside root by $\lambda$, so $|\lambda|>1$.

To identify these as the eigenvalues of $T$, note that

\nopagebreak[4]

$$
U(z)=e^T(I-zT)^{-1}e.
$$

The right side has denominator dividing the degree-at-most-four polynomial $\det(I-zT)$. Lemma 1 says that the reduced denominator on the left is exactly the degree-four polynomial $d(z)$, up to a nonzero scalar. Since both constant terms are nonzero, it follows that

\nopagebreak[4]

$$
\det(I-zT)=d(z)/a.
\tag{15}
$$

Thus $T$ is diagonalizable with precisely the roots of $p$ as its eigenvalues. Let $\Pi$ be its rank-one spectral projector for $\lambda$. The scalar

\nopagebreak[4]

$$
\gamma=e^T\Pi e
\tag{16}
$$

is nonzero: otherwise $e^T(I-zT)^{-1}e$ would have no pole at $z=1/\lambda$, contradicting Lemma 1. Consequently there are matrices $R_j$ and scalars $b_j$, uniformly bounded for integers $j\ge0$, such that

\nopagebreak[4]

$$
T^j=\lambda^j\Pi+R_j,\qquad
 a_j:=e^TT^je=\gamma\lambda^j+b_j.
\tag{17}
$$

The uniform bounds follow because all other eigenvalues have modulus at most one and are simple. In particular $a_n\ne0$ for every sufficiently large $n$, and

\nopagebreak[4]

$$
d_n:=\frac{a_n}{\gamma\lambda^n}=1+O_r(|\lambda|^{-n}),
\qquad |d_n|\ge\tfrac12
\tag{18}
$$

for all sufficiently large $n$.

## 4. The finite Green matrix has bounded entries

For such $n$, the boundary problem (4) has the unique solution

\nopagebreak[4]

$$
u_0=-a_n^{-1}\sum_{\ell=0}^{n-1}e^TT^{n-1-\ell}Gf_\ell,
$$

and, for $0\le j\le n$,

\nopagebreak[4]

$$
w_j=\sum_{\ell=0}^{n-1}K_{j\ell}^{(n)}f_\ell,
\quad
K_{j\ell}^{(n)}=
\mathbf 1_{\{\ell<j\}}T^{j-1-\ell}G
-T^je\,a_n^{-1}e^TT^{n-1-\ell}G.
\tag{19}
$$

We claim that all these $4\times2$ matrices have norm bounded by a constant depending only on $r$, independent of $n,j,\ell$.

\Needspace{5\baselineskip}

Since $\Pi$ has rank one, (16) implies

\nopagebreak[4]

$$
\Pi e e^T\Pi=\gamma\Pi.
$$

Substituting (17) and (18) into the second term of (19), its contribution with two projectors is

\nopagebreak[4]

$$
\frac{\lambda^{j-1-\ell}}{d_n}\Pi G.
\tag{20}
$$

The three other contributions are respectively

\nopagebreak[4]

$$
\begin{aligned}
&\frac{\lambda^{j-n}}{\gamma d_n}\Pi e e^TR_{n-1-\ell}G,\\
&\frac{\lambda^{-1-\ell}}{\gamma d_n}R_je e^T\Pi G,\\
&\frac{\lambda^{-n}}{\gamma d_n}R_je e^TR_{n-1-\ell}G.
\end{aligned}
\tag{21}
$$

They are uniformly bounded: all powers of $\lambda$ appearing in (21) have nonpositive exponents, and all the remaining factors are uniformly bounded.

If $\ell\ge j$, the first term of (19) is absent, and (20) is uniformly bounded because $j-1-\ell\le-1$. If $\ell<j$, the projector part of the first term in (19) cancels (20) up to

\nopagebreak[4]

$$
\lambda^{j-1-\ell}(1-d_n^{-1})\Pi G.
$$

This is uniformly bounded, since $1-d_n^{-1}=O_r(|\lambda|^{-n})$ and $j-1-\ell\le n-1$. The remaining contribution $R_{j-1-\ell}G$ is uniformly bounded as well. This proves the claim.

Let $C_r$ bound these norms. Then (19) and Cauchy--Schwarz give

\nopagebreak[4]

$$
\|w_j\|_2\le C_r\sum_{\ell=0}^{n-1}\|f_\ell\|_2
\le C_r\sqrt n\,\|f\|_2.
$$

Every $u_j$ for $0\le j<n$ is the first coordinate of $w_j$, and every $v_j$ for $0\le j<n$ is the second coordinate of $w_{j+1}$. Summing the resulting squared bounds gives

\nopagebreak[4]

$$
\|M_n^{-1}f\|_2\le \sqrt2 C_r n\,\|f\|_2.
\tag{22}
$$

Finally, the bandwidth and all coefficient blocks of $M_n$ are fixed once $r$ is fixed. The block-shift representation gives

\nopagebreak[4]

$$
\|M_n\|_2\le\sum_{k=-1}^{2}\|80(iB_k-rC_k)\|_2=:D_r<\infty,
$$

uniformly in $n$. Since multiplication by $80$ does not change the condition number, (22) proves the theorem with $K_r=\sqrt2 C_rD_r$. Eventual invertibility was established in (18)--(19). $\square$

\Needspace{13\baselineskip}

## Scope and source

The conclusion concerns every fixed positive real parameter, including $r=\sqrt{10}$, and the exact finite Toeplitz truncations in MF-22. It makes no uniform-in-parameter claim and does not add or remove boundary entries. Finitely many small sizes are permitted by the target's eventual formulation.

The block coefficients, scalar symbol quartic, and prior open status are in M. Bogoya, A. Böttcher, M. Ferrari, S. M. Grudsky and S. Serra-Capizzano, *Condition numbers of block Toeplitz matrices and stability of space-time IgA approximations for the wave and Schrödinger equations*, [arXiv:2608.24151v1](https://arxiv.org/html/2608.24151v1), equation (5.22), §5.3 equation (5.32), Proposition 5.14, and the paragraph after Figure 9. The recurrence, coprimality calculation, and finite Green-kernel estimate above supply the proposed additional argument.
