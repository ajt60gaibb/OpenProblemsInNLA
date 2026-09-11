---
title: "A cubic-time Schur algorithm with logarithmic mantissa precision"
author: "Matthew J. Colbrook"
affiliation: "Department of Applied Mathematics and Theoretical Physics, University of Cambridge, Cambridge, United Kingdom"
email: "m.colbrook@damtp.cam.ac.uk"
document-kind: "RESOLUTION"
review-footer: "Independent Codex-agent verification; no external human peer review or formal certification."
date: "11 September 2026"
lang: "en-GB"
---

**Status of this manuscript:** Independently checked affirmative resolution (Codex-agent review).  
**Target:** [IE-08, original catalog snapshot](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/b4123194697bdf6f8f82518c1dd7d6c40a30c2e0/eigenvalues-and-inverse-problems/IE-08/README.md).  
**Reviewed:** 11 September 2026.

The original proof draft was generated in a ChatGPT conversation. A separate Codex agent independently checked the complete argument against the exact target; its [detailed review](../../references/colbrook-additional-2026-09-11/verification/reviews/IE-08-review.md) records **PASS**. The mathematical sections below are unchanged from the reviewed draft. This is independent agent verification, not external human peer review or a formal proof certificate. The [submission record](../../references/colbrook-additional-2026-09-11/README.md) preserves the original manuscript and verification history.

# Statement and computational model

All unqualified matrix norms are spectral norms. For a diagonalizable matrix $M$, write
$$
 \kappa_V(M)=\inf_{M=V\Lambda V^{-1}}\|V\|\,\|V^{-1}\|,
 \qquad
 \operatorname{gap}(M)=\min_{i\ne j}|\lambda_i-\lambda_j|,
$$
where the eigenvalues in the gap are counted with multiplicity. In particular, a positive gap means that the spectrum is simple.

**Theorem 1 (proposed answer to IE-08).** There are universal constants $C,c>0$ and a randomized floating-point algorithm with the following property. Given $A\in\mathbb C^{n\times n}$, $\|A\|\le1$, and $0<\delta<1/2$, it uses at most
$$
 Cn^3\log^c(n/\delta)
$$
arithmetic operations, with at most $C\log(n/\delta)$ mantissa bits per real component, and returns matrices $Q,T$. The matrix $T$ is exactly upper triangular. With probability at least $0.99$,
$$
 \|A-QTQ^*\|\le\delta,
 \qquad \|Q^*Q-I\|\le\delta.
$$
No separation, simplicity, or diagonalizability assumption is imposed on the input.

The model is ordinary relative-error floating-point arithmetic, including real square roots, with sufficient exponent range. Inputs and all intermediate scalars are represented at the stated precision. Complex arithmetic is implemented by a constant number of real operations. Randomness consists of finitely many unbiased bits. No exact eigensolver, exact Gaussian oracle, multiword precision simulation, or matrix-function oracle is used. The classical cubic-time Householder QR and triangular-solve kernels are used, rather than fast inversion with a condition-number exponent depending on $n$.

The target is the displayed formulation of IE-08 and the ordinary Schur problem in Problem 3.3 of the workshop report.[^repo] It is not a claim about nearly matrix-multiplication-time algorithms, a deterministic algorithm, generalized matrix pencils, or a practical double-precision implementation.

[^repo]: *Open Problems in Numerical Linear Algebra*, IE-08, “A cubic-time Schur algorithm using logarithmic precision,” formulation checked 11 September 2026; [canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IE-08/README.md). N. Amsel et al., *Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*, arXiv:2602.05394v3, Problem 3.3, [source](https://arxiv.org/html/2602.05394v3#S3.SS2).

The proof has three components. First, a contour estimate controls every remaining composition of Newton's sign iteration uniformly, so local errors accumulate additively instead of through a product of one-step bounds. Second, a global backward-error representation controls all diagonal blocks at every subdivision level. Third, a finite random grid and finite Gaussian sampling provide uniform polynomial separation and rank-revelation bounds.

# Classical floating-point kernels

We use the following conventional bounds. A single sufficiently large universal constant $C_0$ may absorb all constants in this section and below.

**Lemma 2 (classical kernels).** For matrices of order at most $m$, and unit roundoff $u$ sufficiently small compared with the displayed conditioning factors, classical algorithms give the following guarantees in $O(m^3)$ arithmetic operations.

(a) Matrix multiplication satisfies
$$
 \|\operatorname{fl}(XY)-XY\|\le C_0m^6u\|X\|\|Y\|.
$$
The corresponding bound for addition has right-hand side $C_0m^6u(\|X\|+\|Y\|)$.

(b) Householder QR of an $m\times r$ matrix, $r\le m$, with a full unitary completion, produces a stored $\widehat Z$ and an upper-trapezoidal $\widehat R$ for which there is an exactly unitary $Z$ such that
$$
 \|\widehat Z-Z\|\le C_0m^6u,
 \qquad Y+\Delta=Z\widehat R,
 \qquad \|\Delta\|\le C_0m^6u\|Y\|.
$$
Here the first $r$ columns give the thin factorization whenever $Y$ has full column rank.

(c) Inversion by Householder QR followed by triangular solves produces $\operatorname{INV}(Y)$ with
$$
 \|\operatorname{INV}(Y)-Y^{-1}\|
 \le C_0m^6u\|Y\|\|Y^{-1}\|^2,
 \tag{1}
$$
provided $C_0m^6u\kappa_2(Y)\le1/4$.

**Justification.** The usual componentwise dot-product bound is converted to a spectral-norm bound using $\|X\|_F\le\sqrt m\|X\|$. A product of $m$ backward-stable Householder transformations gives (b); using the exponent $6$ instead of the sharp dimension factor leaves ample room for the conversion between norms and for complex arithmetic. These are the standard classical QR guarantees, also used as the QR black box in Banks et al., Definition 2.8 and the discussion following Remark 2.9.[^kernels]

For completeness, (c) follows from (b) and the componentwise backward error of triangular back substitution. For the $m$ right-hand sides together, the residual obeys
$$
 \|Y\widehat X-I\|
 \le C_0m^6u(1+\|Y\|\|\widehat X\|).
$$
Multiplication by $Y^{-1}$ and the smallness assumption absorb the term containing $\widehat X$, giving $\|\widehat X\|\le2\|Y^{-1}\|$ after enlarging $C_0$. Substituting this bound in the residual and multiplying once more by $Y^{-1}$ proves (1). Thus the conditioning exponent in (1) is fixed: it is not $O(\log m)$.

[^kernels]: J. Banks, J. Garza-Vargas, A. Kulkarni, and N. Srivastava, *Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*, arXiv:1912.08805, §1.1.2 and §2.5, especially Definition 2.8 and the paragraph after Remark 2.9, printed pp. 6 and 20; [manuscript](https://arxiv.org/pdf/1912.08805). See also N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, SIAM, 2002, for the classical Householder and triangular-solve analysis; [publisher/author information](https://nhigham.com/accuracy-and-stability-of-numerical-algorithms/).

# A uniformly stable sign iteration

Let
$$
 f(z)=\frac12(z+z^{-1}),\qquad f^0(z)=z,
$$
where $f^j$ denotes composition, not an ordinary power. On the two open half-planes, every $f^j$ is analytic and preserves the sign of the real part. This follows from
$$
 \Re f(z)=\frac{\Re z}{2}\left(1+|z|^{-2}\right).
$$

**Lemma 3 (scalar orbit bounds).** Suppose $|z|\le R_0$, $|\Re z|\ge a$, $R_0\ge1$, and $0<a\le1$. Put
$$
 B=\frac{(R_0+1)^2}{a}\ge4.
$$
Then, for every $j\ge0$,
$$
 |f^j(z)|\le B,
 \qquad |\Re f^j(z)|\ge B^{-1}.
 \tag{2}
$$
For $\Re z>0$, setting $w=(z-1)/(z+1)$ gives
$$
 1-|w|\ge\frac2B,
 \qquad
 f^j(z)=\frac{1+w^{2^j}}{1-w^{2^j}}.
 \tag{3}
$$
For $\Re z<0$, use oddness.

**Proof.** For the positive half-plane,
$$
 1-|w|^2=\frac{4\Re z}{|z+1|^2}\ge\frac4B.
$$
Since $1+|w|\le2$, this implies the first part of (3). The second part follows by substituting into Newton's recurrence. For $q=w^{2^j}$,
$$
 \left|\frac{1+q}{1-q}\right|\le\frac2{1-|w|}\le B,
$$
and
$$
 \Re\frac{1+q}{1-q}
 =\frac{1-|q|^2}{|1-q|^2}
 \ge\frac{1-|q|}{1+|q|}
 \ge\frac{1-|w|}{2}\ge B^{-1}.
$$
This proves (2).

**Lemma 4 (uniform remaining-composition bound).** Let $M=V\Lambda V^{-1}$ satisfy $\kappa_2(V)\le K$, and suppose its eigenvalues satisfy the hypotheses of Lemma 3. Define
$$
 X_j=f^j(M),\qquad
 \rho=\frac1{4KB},\qquad
 L=4096K^2B^6.
 \tag{4}
$$
For every $j,r\ge0$, and every $W_1,W_2$ with $\|W_i-X_j\|\le\rho$,
$$
 \|f^r(W_1)-f^r(W_2)\|\le L\|W_1-W_2\|.
 \tag{5}
$$
In particular, the bound is independent of the number $r$ of remaining iterations.

**Proof.** Use the positively oriented boundaries $\Gamma$ of the two rectangles
$$
 [1/(2B),2B]+i[-2B,2B],
 \qquad [-2B,-1/(2B)]+i[-2B,2B].
$$
Their total perimeter is at most $24B$. By (2), the spectrum of every $X_j$ is inside the rectangles at distance at least $1/(2B)$ from the boundaries. Since all $X_j$ have the same diagonalizing matrix $V$,
$$
 \|(zI-X_j)^{-1}\|\le2KB\quad(z\in\Gamma).
$$
A Neumann series gives $\|(zI-W_i)^{-1}\|\le4KB$. The straight-line homotopy from $X_j$ to $W_i$ has no eigenvalue on $\Gamma$, so all eigenvalues of $W_i$ remain inside these rectangles.

For $z\in\Gamma$, one has $|z|\le3B$ and $|\Re z|\ge1/(2B)$. Applying Lemma 3 with these enlarged parameters gives, uniformly in $r$,
$$
 |f^r(z)|\le2B(3B+1)^2\le32B^3.
$$
The functions are analytic inside both rectangles. The matrix Cauchy formula and the resolvent identity therefore imply
$$
 \begin{aligned}
 \|f^r(W_1)-f^r(W_2)\|
 &\le\frac{24B}{2\pi}\,32B^3(4KB)^2\|W_1-W_2\|\\
 &\le4096K^2B^6\|W_1-W_2\|.
 \end{aligned}
$$
This proves (5). No commutation between the perturbations and the exact iterates is assumed.

**Lemma 5 (inexact iteration).** Let $N\ge1$. Suppose
$$
 \|Y_0-M\|\le e,
 \qquad Y_{j+1}=f(Y_j)+E_j,
 \qquad\|E_j\|\le e\quad(0\le j<N).
$$
If
$$
 e\le\frac{\rho}{4(N+1)L^2},
 \tag{6}
$$
then every iteration is well defined and
$$
 \|Y_j-X_j\|\le(j+1)Le\quad(0\le j\le N).
 \tag{7}
$$

**Proof.** Inductively, (6)--(7) put $Y_s$ within $\rho/(4L)$ of $X_s$. By Lemma 4 with $r=1$, $f(Y_s)$ is within $\rho/4$ of $X_{s+1}$, and $Y_{s+1}$ is within $\rho/2$ after its local error is included. Thus all required spectra lie in the two rectangles, and the rational compositions below exist. For any $j\le N$, telescope exactly:
$$
 \begin{aligned}
 Y_j-f^j(M)
 ={}&f^j(Y_0)-f^j(M)\\
 &+\sum_{s=0}^{j-1}\left[
 f^{j-s-1}(Y_{s+1})-
 f^{j-s-1}(f(Y_s))\right].
 \end{aligned}
 \tag{8}
$$
The first term is bounded by $Le$. In each summand, the two arguments are within $\rho$ of $X_{s+1}$, so Lemma 4 bounds it by $L\|E_s\|\le Le$. This gives (7), completing the induction.

**Corollary 6 (logarithmic-precision sign computation).** Under Lemma 4's assumptions, a forward approximation to $\operatorname{sign}(M)$ of error at most $\varepsilon$, $0<\varepsilon<1$, can be obtained in
$$
 O\!\left(m^3\log\frac{mKB}{\varepsilon}\right)
$$
operations with $O(\log(mKB/\varepsilon))$ mantissa bits, where $m$ is the order of $M$. Known upper and lower bounds on the parameters suffice; no eigenvectors are computed.

**Proof.** Take
$$
 N=\left\lceil\log_2\frac{16BK}{\varepsilon}\right\rceil.
 \tag{9}
$$
By (3), $|w|^{2^N}\le\exp(-32K/\varepsilon)$. The scalar error relative to $\pm1$, multiplied by $K$, is at most $\varepsilon/2$. Thus $\|X_N-\operatorname{sign}(M)\|\le\varepsilon/2$.

When $\|Y_j-X_j\|\le\rho$, (2) gives
$$
 \|Y_j\|\le2KB,
 \qquad \|Y_j^{-1}\|\le2KB.
$$
Lemma 2 therefore bounds the local error of the rounded update
$$
 Y_{j+1}=\operatorname{fl}\!\left(\frac{Y_j+\operatorname{INV}(Y_j)}2\right)
$$
after enlarging $C_0$ by
$$
 e\le C_0m^6u(KB)^3.
 \tag{10}
$$
Choose $u$ so that the right-hand side is at most both $\rho/[4(N+1)L^2]$ and $\varepsilon/[2(N+1)L]$. A rounded input or a rounded scalar shift can be included as the initial error in Lemma 5. All required smallness bounds are inverse polynomials in $m,K,B,\varepsilon^{-1},N$, with fixed exponents. Their logarithms are $O(\log(mKB/\varepsilon))$. Lemma 5 supplies the other half of the error budget.

# Robustness and conditioning of every recursive block

**Lemma 7 (robust diagonalization).** Suppose $M=V\Lambda V^{-1}$ has simple spectrum, $\kappa_2(V)\le K$, and gap at least $g$. If
$$
 \|F\|\le\frac{g}{16\sqrt n K},
$$
then $M+F$ has simple spectrum, each eigenvalue is matched to a unique eigenvalue of $M$ within $K\|F\|$, and
$$
 \kappa_V(M+F)\le3K.
 \tag{11}
$$

**Proof.** Put $E=V^{-1}FV$, so $\|E\|\le K\|F\|$. The Bauer--Fike disks are disjoint; applying the same inclusion along the homotopy $\Lambda+tE$ shows that each disk contains exactly one eigenvalue, counted with algebraic multiplicity. For the eigenvalue $\mu_i$ matched to $\lambda_i$, normalize its eigenvector to have coordinate $i$ equal to one. This normalization is possible: otherwise the complementary principal system would have a nonzero null vector, contradicting its invertibility. Write the eigenvector as $e_i+y_i$, with $(y_i)_i=0$. On the complementary coordinates, the diagonal part is at distance at least $g-\|E\|$ from zero, so the perturbed system is invertible with inverse norm at most $2/g$. Consequently
$$
 \|y_i\|\le2\|E\|/g.
$$
For the matrix $Y$ with columns $y_i$,
$$
 \|Y\|\le\|Y\|_F\le2\sqrt n\|E\|/g\le1/8.
$$
Thus $V(I+Y)$ diagonalizes $M+F$ and has condition number at most $K(1+1/8)/(1-1/8)<3K$.

**Lemma 8 (global projector control).** Suppose $S$ is upper block triangular, has simple spectrum, and $\kappa_V(S)\le K$. Every diagonal block $C$ of order $m$ satisfies
$$
 \kappa_V(C)\le mK.
 \tag{12}
$$

**Proof.** The spectral projector of $S$ for a simple eigenvalue $\lambda_i$ is the polynomial
$$
 p_i(S),\qquad
 p_i(z)=\prod_{j\ne i}\frac{z-\lambda_j}{\lambda_i-\lambda_j},
$$
and its norm is at most $K$ (or arbitrarily close to $K$ if the infimum defining $\kappa_V$ is used). Its diagonal block in $C$ is $p_i(C)$, the corresponding spectral projector of $C$ when $\lambda_i\in\sigma(C)$. Compression cannot increase the spectral norm.

Normalize the right eigenvectors of $C$ to have norm one and put them in a matrix $W$. Each row of $W^{-1}$ has norm equal to the norm of its associated rank-one projector, hence at most $K$. Therefore $\|W\|\le\sqrt m$ and $\|W^{-1}\|\le\sqrt mK$, proving (12).

The point of (12) is that it is applied to the same full working matrix at each level. Its factors are not multiplied down the recursion.

# Random regularization and finite sampling

We now choose one large dyadic parameter. Let $R$ be a power of two satisfying
$$
 R\ge\max\left\{2^{40},C_0^{100},10^{24}(n/\delta)^{10}\right\},
 \tag{13}
$$
within a factor of two of the right-hand side. Enlarge $C_0$ once for all harmless numerical constants below. Thus
$$
 \log R=O(\log(n/\delta)),\qquad n\le R,\qquad\delta^{-1}\le R.
$$
Work throughout with
$$
 u\le R^{-2000}.
 \tag{14}
$$
All exponents here are fixed universal constants; they are intentionally not optimized.

**Lemma 9 (finite Gaussian samples).** The algorithm can generate every Gaussian sample used below, using finitely many random bits and $\operatorname{polylog}R$ operations per complex entry at precision (14), so that there are corresponding independent standard complex Gaussian entries $G$ with
$$
 |\widehat G-G|\le R^{-800},\qquad |G|\le R,
 \tag{15}
$$
simultaneously for at most $R^3$ entries, except on an event of probability at most $R^{-15}$. The operation count is deterministically capped.

**Proof.** A standard complex Gaussian has the Box--Muller representation
$$
 G=\sqrt{-\log U_1}\,\exp(2\pi iU_2),
$$
where $U_1,U_2$ are independent uniform variables on $(0,1)$. Generate dyadic mesh approximations with mesh $R^{-1000}$ and couple them to continuous uniforms in their mesh cells. Abort when a stored radial uniform is within $2R^{-20}$ of either endpoint. Outside an event of probability at most $8R^{-20}$ per entry, the continuous and stored radial uniforms lie in $[R^{-20},1-R^{-20}]$. On this interval the derivatives of the displayed functions are bounded by fixed powers of $R$. In particular, excluding the upper endpoint avoids the square-root singularity at $U_1=1$ as well as the logarithmic singularity at zero. Mesh error is therefore much smaller than $R^{-800}$.

The required functions can be evaluated at the same precision using range reduction and convergent series. Write $U_1=2^kv$, $v\in[1,2]$, and use
$$
 \log v=2\sum_{j\ge0}\frac{w^{2j+1}}{2j+1},\qquad
 w=\frac{v-1}{v+1},\quad |w|\le1/3.
$$
Compute $\log2$ by the same series, and $\pi$ by a fixed Machin arctangent identity. Taylor series for sine and cosine on a bounded interval converge to the necessary accuracy in $O(\log R)$ terms. Range reduction takes $O(\log R)$ steps on the retained interval. Rounding errors, accumulated over these polynomially logarithmic lengths and multiplied by fixed polynomial conditioning bounds, are smaller than $R^{-800}$ under (14). Real square roots obey the usual relative-error model. All loops have fixed caps determined by $R$.

Each mesh integer has at most $1000\log_2 R$ bits, fewer than the available mantissa bits. Thus neither the mesh integers nor the function evaluation use a higher-precision representation. A union bound over at most $R^3$ entries gives failure probability at most $8R^{-17}<R^{-15}$. On the retained interval, $|G|=\sqrt{-\log U_1}\le\sqrt{20\log R}<R$.

**Lemma 10 (regularized starting matrix).** For $n\ge2$, in $O(n^2\operatorname{polylog}R)$ operations one can compute a stored matrix $M_0$ for which, with probability at least $0.999$,
$$
 \|M_0-A\|\le\delta/3,
 \quad \|M_0\|\le2,
 \quad \kappa_V(M_0)\le R,
 \quad \operatorname{gap}(M_0)\ge R^{-1}.
 \tag{16}
$$

**Proof.** Let $\gamma=\delta/16$ and let $G_n$ have independent standard complex Gaussian entries scaled by $1/\sqrt n$. Theorem 3.6 of Banks et al. gives[^regularize]
$$
 \begin{aligned}
 &\Pr\bigl[\kappa_V(A+\gamma G_n)<t,
      \operatorname{gap}(A+\gamma G_n)>r,
      \|G_n\|<4\bigr]\\
 &\quad\ge1-
 \left(576\frac{t^8r^6n^8}{\gamma^8}
       +\frac{9n^3}{\gamma^2t^2}+2e^{-2n}\right).
 \end{aligned}
 \tag{17}
$$
Choose
$$
 t=10^4n^2/\gamma,
 \qquad r=\gamma^4/(10^{12}n^5).
$$
The first two failure terms sum to less than $10^{-6}$. For $n\ge5$, the last term is less than $10^{-4}$. For $n=2,3,4$, inspect the proof of (17): that last term only bounds $\Pr(\|G_n\|\ge4)$, so it may be replaced by the following smaller elementary estimate. Since $n\|G_n\|_F^2$ is a sum of $n^2$ independent mean-one exponential variables,
$$
 \Pr(\|G_n\|\ge4)
 \le \Pr(n\|G_n\|_F^2\ge16n)
 \le e^{-8n}2^{n^2}<2\cdot10^{-6}.
$$
Thus the continuous event in (17) has probability greater than $0.9998$ in all dimensions $n\ge2$.

Compute $M_0=\operatorname{fl}(A+\gamma\widehat G_n)$ using Lemma 9. The total sampling, input, scaling, and addition error relative to $A+\gamma G_n$ is at most $R^{-500}$. The choice (13) dominates $100t$ and $100/r$. Apply Lemma 7 to this tiny perturbation; it preserves the bounds in (16) with room to spare. Also $\|\gamma G_n\|\le\delta/4$, so the perturbation bound and norm bound in (16) follow. Include Lemma 9's failure event in the stated $0.001$ budget.

[^regularize]: Banks et al., *Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*, arXiv:1912.08805, Theorem 3.6 and its proof, printed pp. 23--24; [source](https://arxiv.org/pdf/1912.08805). The present proof combines that theorem with an explicit finite sampler and the elementary perturbation lemma above.

# One random grid for all subdivision levels

Set
$$
 H=\log_2R+10,\qquad h=8/2^H=\frac1{128R},
 \qquad\eta=R^{-10}.
 \tag{18}
$$
Independently of $M_0$, choose $\alpha,\beta$ uniformly from the finite dyadic set
$$
 \left\{\frac{jh}{R^{20}}:0\le j<R^{20}\right\}.
$$
The root square is
$$
 [\alpha-4,\alpha+4]\times[\beta-4,\beta+4]
$$
after identifying $\mathbb C$ with $\mathbb R^2$. It contains the spectrum of $M_0$. Bisect each coordinate $H$ times. Every line used in these nested bisections is a line of the finest grid $\alpha+h\mathbb Z$ or $\beta+h\mathbb Z$.

**Lemma 11 (simultaneous grid margin).** Conditional on (16), except with probability at most
$$
 512R^{-8}+4R^{-19},
 \tag{19}
$$
every eigenvalue of $M_0$ has distance at least $\eta$ from every vertical and horizontal grid line.

**Proof.** For a fixed real coordinate $x$, the fraction of offsets $\alpha$ for which $\operatorname{dist}(x,\alpha+h\mathbb Z)<\eta$ is at most
$$
 2\eta/h+2/R^{20}.
$$
This follows by counting mesh points in an interval of total length $2\eta$ on the circle of circumference $h$. Union-bound over two coordinates of $n\le R$ eigenvalues to obtain (19).

No grid line is chosen using an eigenvalue oracle. The eigenvalues in this lemma appear only in the analysis. All offsets, endpoints, and midpoints are dyadic numbers using $O(\log R)$ bits and are exactly representable at (14).

# Extracting one approximate invariant subspace

We first record a quantitative rank-revelation fact that works for nonorthogonal projectors.

**Lemma 12 (Gaussian range extraction).** Let $P^2=P$ be an $m\times m$ projector of rank $r$, with $1\le r<m$. If $\Omega$ is an independent $m\times r$ standard complex Gaussian matrix, then
$$
 \Pr\bigl[\sigma_r(P\Omega)<t\bigr]\le r^2t^2.
 \tag{20}
$$

**Proof.** Relative to the orthogonal splitting by its range, an idempotent has the form
$$
 P=\begin{pmatrix}I&F\\0&0\end{pmatrix},
$$
so all of its nonzero singular values are at least one. In a thin singular-value decomposition $P=U_r\Sigma V_r^*$, the matrix $G=V_r^*\Omega$ is an $r\times r$ standard complex Gaussian. Therefore $\sigma_r(P\Omega)\ge\sigma_r(G)$.

If $\sigma_r(G)<t$, choose a unit vector $v$ with $\|Gv\|<t$ and a coordinate $j$ with $|v_j|\ge1/\sqrt r$. The $j$th column of $G$ is then at distance less than $\sqrt r\,t$ from the span of the other columns. Conditional on those columns, its orthogonal projection onto their one-dimensional complex orthogonal complement is a standard complex Gaussian scalar. The small-ball probability is at most $rt^2$. A union bound over $j$ proves (20).

Suppose now that $C$ is a current diagonal block, $\|C\|\le3$, its eigenvector condition number is at most $R^3$, and its spectrum has distance at least $\eta/2$ from the proposed cut line. For a vertical cut at $s$, put $M=C-sI$; for a horizontal cut at $s$, put $M=-iC-sI$. In either case $\|M\|\le8$. The spectral projector for the left or lower side is
$$
 P=\frac{I-\operatorname{sign}(M)}2.
 \tag{21}
$$
Compute an approximation $\widetilde P$ with
$$
 \|\widetilde P-P\|\le\tau,
 \qquad\tau=R^{-300},
 \tag{22}
$$
using Corollary 6. The precision audit below verifies that (14) suffices.

The rank $r$ is the nearest integer to the computed real trace of $\widetilde P$. Indeed, $\operatorname{tr}P=r$ exactly, and the trace error is bounded by $m\tau$ plus a polynomial-times-$u$ summation error, less than $1/4$. If $r=0$ or $r=m$, no basis computation is needed. The block is passed to the appropriate child cell.

Otherwise, generate a finite Gaussian $\widehat\Omega$, form the rounded product $\widetilde P\widehat\Omega$, and compute a full Householder QR completion $\widehat Z$. On the event in Lemma 9 and the event $\sigma_r(P\Omega)\ge R^{-20}$ from Lemma 12,
$$
 \|\Omega\|\le R^2,
 \qquad
 \|\operatorname{fl}(\widetilde P\widehat\Omega)-P\Omega\|
 \le R^{-297}.
 \tag{23}
$$
The QR backward error is much smaller than this. Thus the exactly unitary matrix $Z$ associated with $\widehat Z$ in Lemma 2 has its first $r$ columns spanning a subspace at angle at most $R^{-270}$ from $\operatorname{range}P$. Here one may use the elementary bound
$$
 \|\sin\Theta(\operatorname{range}Y,\operatorname{range}(Y+E))\|
 \le \frac{\|E\|}{\sigma_r(Y)-\|E\|}.
$$
There is consequently an exactly unitary $Z_0$ whose first $r$ columns span the exact invariant range of $P$ and
$$
 \|Z-Z_0\|\le3R^{-270}.
 \tag{24}
$$
For example, take the direct rotation between the two subspaces and apply it to the full frame $Z$. Since $Z_0^*CZ_0$ has zero lower-left block,
$$
 \|(Z^*CZ)_{21}\|\le R^{-260}.
 \tag{25}
$$
The strict exponents in (23)--(25) absorb fixed constants. Conditional on the prior computation, (20) bounds the bad rank-revelation event by $r^2R^{-40}\le R^{-38}$. Conditioning is legitimate because each new Gaussian is independent of the current block.

# The complete levelwise algorithm

Maintain an exactly upper-block-triangular stored matrix $S$, a partition into contiguous diagonal blocks, a grid cell assigned to each block, and a stored product $\widehat Q$. Initially
$$
 S=M_0,\qquad\widehat Q=I,
$$
with one root cell and one block.

Perform $2H$ subdivision levels, alternating vertical and horizontal bisection. At each level, for every nonscalar diagonal block, apply the preceding section to the midpoint of its cell in the chosen coordinate. A rank-zero or full-rank split changes only the cell assignment. A nontrivial split produces a full basis $\widehat Z$ and two child blocks, placed in left/right or lower/upper order. Scalar blocks can simply be retained without further computation.

Assemble the bases for that level into one block-diagonal stored matrix $\widehat Y_\ell$; use identity blocks wherever no basis change is needed. Update
$$
 S\leftarrow\operatorname{fl}(\widehat Y_\ell^*S\widehat Y_\ell),
 \qquad
 \widehat Q\leftarrow\operatorname{fl}(\widehat Q\widehat Y_\ell).
 \tag{26}
$$
Set the new lower-left blocks exactly to zero. Preserve the existing structural zero blocks by blockwise computation or by resetting them to zero. This ensures exact upper-block-triangular structure at every level.

If all final blocks are scalar, return $T=S$ and $Q=\widehat Q$. Otherwise return a fixed dummy output. Every loop, including every sign iteration and every sampling loop, is capped by the parameters above. The algorithm also returns the dummy output on an invalid rounded rank, a failed or unsafe factorization, or an oversized intermediate matrix. The thresholds can be chosen as fixed powers of $R$ below the precision budget. The analysis shows that none of these aborts occurs on the good events. This makes the operation bound worst-case, not merely expected.

# Global backward error and correct spectral labels

The following induction is the main reason the precision does not grow with recursion depth.

For each level choose the exactly unitary block-diagonal $Z_\ell$ close to $\widehat Y_\ell$ supplied by Lemma 2. Let
$$
 W_\ell=Z_1\cdots Z_\ell.
$$
The invariant is
$$
 S_\ell=W_\ell^*(M_0+F_\ell)W_\ell,
 \qquad\|F_\ell\|\le\ell R^{-250}.
 \tag{27}
$$
Every eigenvalue in each active block is matched to a unique original eigenvalue of $M_0$ lying in the block's assigned cell.

At level zero this is immediate. Suppose it holds before a level. Since $2H\le R$,
$$
 \|F_\ell\|\le R^{-249}<\mu,
 \qquad\mu=R^{-100}.
$$

Lemma 7 and (16) then give
$$
 \kappa_V(M_0+F_\ell)\le3R,
 \qquad
 |\lambda_i(M_0+F_\ell)-\lambda_i(M_0)|\le R\mu.
 \tag{28}
$$
The perturbation assumption in Lemma 7 is satisfied because $\mu\ll R^{-1}/(16\sqrt n R)$. In particular the spectrum remains simple, its gap is at least $1/(2R)$, and $\|S_\ell\|\le3$.

By Lemma 8, each active block $C$ satisfies
$$
 \kappa_V(C)\le3mR\le R^3.
 \tag{29}
$$
The original-grid margin $\eta$ and (28) put every current eigenvalue at distance at least $\eta/2$ from every cut line. Thus all assumptions of the subspace extraction section hold uniformly.

The local lower-left errors in (25) occupy disjoint diagonal parent blocks. The norm of their direct sum is their maximum, not their sum. The matrix-product error in (26), the difference between stored and exactly unitary bases, and the deliberate zeroing therefore give
$$
 S_{\ell+1}=Z_{\ell+1}^*S_\ell Z_{\ell+1}+E_{\ell+1},
 \qquad\|E_{\ell+1}\|\le R^{-250}.
 \tag{30}
$$
All constants and polynomial dimension factors are absorbed by the unused ten powers between (25) and (30), and by (14). Conjugating (30) by $W_{\ell+1}$ proves (27) at the next level.

It remains to verify that the correct eigenvalue labels pass to the children, rather than merely that the total spectrum is close. At a nontrivial split, compare with the exact invariant transform $Z_0$ in (24). The two diagonal blocks of $Z_0^*CZ_0$ contain precisely the parent eigenvalues on their respective sides of the cut. By Lemma 8 applied to this exact two-block triangularization, each exact child has eigenvector condition number at most $m\kappa_V(C)\le R^4$.

The actual child blocks differ from these exact child blocks by at most $R^{-260}$, after the harmless weakening of (24) and inclusion of rounding. Bauer--Fike, together with the disjoint-disk homotopy argument in Lemma 7, matches each actual child eigenvalue to an eigenvalue of the correct exact child within $R^{-256}$. The exact parent gap is at least $1/(2R)$, while all cut margins are at least $\eta/2$. Hence no label can move to the wrong side. Its match to an eigenvalue of $M_0$ is the unique global match in (28). Rank-zero and full-rank splits have the same label property directly from (21). This completes the induction, including the cell assignment.

After $H$ cuts in each coordinate, any remaining nonscalar cell has side length $h$ and diameter $\sqrt2h<1/(2R)$. It cannot contain two eigenvalues of $M_0$, whose gap is at least $1/R$. The label invariant therefore forces all blocks to be scalar. Thus the returned $T$ is exactly upper triangular.

# Explicit precision audit

For every sign call, (29) gives $K\le R^3$, the shifted matrix has norm at most $8$, and $a\ge\eta/2=R^{-10}/2$. Lemmas 3--5 can consequently use bounds
$$
 B\le162R^{10}\le R^{11},\qquad
 L\le R^{73},\qquad
 \rho\ge R^{-15}.
 \tag{31}
$$
For projector accuracy $\tau=R^{-300}$, use sign accuracy at most $\tau$ before forming (21), with a further fixed factor reserved for addition. Formula (9) gives $N\le R$ and in fact $N=O(\log R)$.

By (10), with (14), the local error, including an initial scalar shift, is bounded by $R^{-1900}$. This is smaller than both
$$
 \frac{\rho}{4(N+1)L^2}
 \quad\text{and}\quad
 \frac{\tau}{4(N+1)L},
$$
whose reciprocals grow by fixed powers no larger than $R^{164}$ and $R^{376}$, respectively, after absorbing constants. The inverse-conditioning condition in Lemma 2 is also satisfied. Thus Corollary 6 supplies (22) uniformly at the same precision.

For range extraction, $\|P\|\le R^3$, $\|\Omega\|\le R^2$, and $\sigma_r(P\Omega)\ge R^{-20}$ on the good event. Sampling and arithmetic errors in the product and QR are negligible compared with $\tau R^2=R^{-298}$. The bound $R^{-297}$ in (23), divided by $R^{-20}$, is at most $R^{-276}$ after constants, which is stronger than the angle allowance $R^{-270}$. This verifies (24)--(25).

Finally, all full matrix updates have norms bounded by fixed powers of $R$, and their dimension is at most $R$. Lemma 2 therefore gives arithmetic errors much smaller than $R^{-250}$. The deliberate discarded blocks, bounded by $R^{-260}$, dominate (30). These estimates also provide explicit polynomial abort thresholds that are never reached on the good events. No precision increase occurs at later levels.

# Success probability, work, and final residual

There are at most $n-1$ nontrivial splits, because each such split increases the number of nonempty diagonal blocks by one. A still looser bound of $n(2H)\le R^2$ suffices. Conditional on the preceding computation, each bad Gaussian range-extraction event has probability at most $R^{-38}$. Their union therefore has probability at most $R^{-36}$. The number of Gaussian entries is at most $n^2+(2H)n^2\le R^3$, as required in Lemma 9.

Combining Lemmas 9--11 and (20), the total failure probability is less than
$$
 0.001+R^{-15}+512R^{-8}+4R^{-19}+R^{-36}<0.01.
$$
Double-counting part of the sampler failure already included in Lemma 10 only makes this upper bound more conservative.

At any level, the diagonal-block orders satisfy $\sum m^3\le n^3$. Each sign computation takes $O(m^3\log R)$ operations, and there are $O(\log R)$ levels. The full transforms and accumulation in (26) each cost $O(n^3)$ per level. QR has the same cubic upper bound. Finite sampling contributes $O(n^2\log R\operatorname{polylog}R)$ operations. The total is therefore $O(n^3\operatorname{polylog}R)$, with a universal logarithmic exponent. The capped implementation has this bound on every execution. The precision (14) is $2000\log_2R+O(1)=O(\log(n/\delta))$ mantissa bits.

On the good event, let $L_0=2H$ and $W=W_{L_0}$. Equation (27) gives
$$
 WT W^*=M_0+F_{L_0},
 \qquad\|F_{L_0}\|\le R^{-249},
 \qquad\|T\|\le3.
$$
The rounded accumulation of near-unitary factors in (26), using Lemma 2 and $L_0\le R$, satisfies
$$
 \|Q-W\|\le R^{-1000}.
$$
For example, iterating
$$
 d_{\ell+1}\le(1+C_0n^6u)d_\ell+C_0n^6u
$$
with enlarged constants gives a much smaller bound. Consequently
$$
 \|Q^*Q-I\|\le2R^{-1000}+R^{-2000}<\delta,
$$
and
$$
 \begin{aligned}
 \|A-QTQ^*\|
 &\le\|A-M_0\|+\|F_{L_0}\|
      +\|WTW^*-QTQ^*\|\\
 &\le\delta/3+R^{-249}
      +3\|Q-W\|(2+\|Q-W\|)\\
 &<\delta.
 \end{aligned}
$$
For $n=1$, return $Q=1$ and the rounded scalar $T=A$ directly. This completes the proposed proof of Theorem 1.

# Scope and verification status

The proposed proof uses the uniform remaining-composition estimate (5), its telescoping use in (8), and the global rather than recursively multiplied conditioning control (27)--(29), combined with conventional smoothed regularization. The proof uses the published Gaussian regularization theorem explicitly; it does not claim that theorem as new.

The constants are deliberately enormous and are intended to establish the asymptotic precision and operation bounds. The accompanying diagnostic code uses ordinary precision and practical parameters to test the algebraic identities and algorithmic mechanisms. It is not an implementation of the conservative parameter choices in this theorem and does not independently verify the general floating-point proof. A separate Codex agent has now audited the complete proof, including its precision analysis, and returned PASS. The repository submission records **Solved**, explicitly identifying this verification level; it does not claim external human peer review or formal certification.

# Sources

1. *Open Problems in Numerical Linear Algebra*, IE-08, canonical statement, checked 11 September 2026. [Repository entry](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/main/eigenvalues-and-inverse-problems/IE-08/README.md).
2. N. Amsel et al., *Linear Systems and Eigenvalue Problems: Open Questions from a Simons Workshop*, arXiv:2602.05394v3, Problem 3.3. [Report](https://arxiv.org/html/2602.05394v3).
3. J. Banks, J. Garza-Vargas, A. Kulkarni, and N. Srivastava, *Pseudospectral Shattering, the Sign Function, and Diagonalization in Nearly Matrix Multiplication Time*, arXiv:1912.08805v5; published in *Foundations of Computational Mathematics* 23 (2023), 1959--2047. Theorem 3.6, printed pp. 23--24 of the arXiv PDF, and §2.5 are the principal imported results. [Manuscript](https://arxiv.org/pdf/1912.08805); [publication](https://doi.org/10.1007/s10208-022-09577-5).
4. N. J. Higham, *Accuracy and Stability of Numerical Algorithms*, second edition, SIAM, 2002. Classical Householder QR, dot-product, and triangular-solve error analysis. [Author's book page](https://nhigham.com/accuracy-and-stability-of-numerical-algorithms/).
