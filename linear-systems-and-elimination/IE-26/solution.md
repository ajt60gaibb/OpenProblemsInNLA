---
title: 'IE-26: Sharp stability bounds for perturbed Fourier interpolation'
author: 'George Stepaniants'
affiliation: 'Department of Computing and Mathematical Sciences, California Institute of Technology, Pasadena, California, USA'
date: '12 September 2026 (UTC)'
document-kind: 'AFFIRMATIVE RESOLUTION'
review-footer: 'Substantial AI assistance; independent automated review is documented separately.'
---

This manuscript proves the two bounds in the original [IE-26 statement](README.md), with the exact square Fourier normalization and all its parameter quantifiers. The conjectures and their prior analysis are due to Austin and Trefethen, with related results in Austin's thesis and the cited later literature. The proof is analytic; finite numerical diagnostics are supplementary.

**Independent review.** A separate [Codex-agent full-target audit](../../references/stepaniants-ie26-2026-09-12/verification/independent-review/IE-26-independent-review.md) returned PASS for both bounds, with no mathematical correction. The [submission record](../../references/stepaniants-ie26-2026-09-12/README.md) preserves the exact frozen source, independent report, and separate coordinating check. The coordinating agent contributed before the source was frozen and is not counted as the independent reviewer. Substantial AI assistance is disclosed; this is informal automated review, not external human peer review or formal verification.

## 1. Exact target and conclusion

Let $m=2N+1$, $N\ge2$, $h=2\pi/m$, and let $a_j=jh$, with the indices taken modulo $m$. Choose arbitrary $s_j\in[-\alpha,\alpha]$, where $0<\alpha<1/2$, and set $x_j=a_j+s_jh$ modulo $2\pi$. Reindexing the original indices $-N,\ldots,N$ cyclically makes no difference. Put $z_j=e^{ix_j}$.

Let $\ell_j$ be the trigonometric cardinal polynomial of degree at most $N$ at these nodes. The Lebesgue constant is

$$\Lambda_N=\sup_x\sum_j|\ell_j(x)|.$$

Let $F=m^{-1/2}[e^{i\nu x_j}]_{j,\nu=-N}^N$ and $\Gamma_N=\|F^{-1}\|_2$.

**Theorem 1.** There is an absolute constant $C$ such that

$$\Lambda_N\le C\frac{N^{2\alpha}-1}{\alpha(1-2\alpha)} \qquad (N\ge2,\ 0<\alpha<1/2). \tag{1}$$

For each fixed $1/4<\alpha<1/2$ there is $C_\alpha$, independent of the nodes and $N$, such that

$$\Gamma_N\le C_\alpha N^{4\alpha-1}. \tag{2}$$

Throughout the proof, $C$ denotes an absolute positive constant, allowed to increase from line to line. Constants marked $C_\alpha$ may depend on $\alpha$. All arcs and distances are circular unless specified otherwise. Circle integrals are with respect to ordinary angular length; fixed factors $2\pi$ are absorbed into absolute constants.

## 2. Interlacing and a positive-real rational function

Define

$$P(z)=\prod_{j=0}^{m-1}(z-z_j),\qquad P_0(z)=z^m-1,\qquad Q(z)=z^m+1,$$

and let

$$\vartheta=\frac h2\sum_j s_j,\qquad R(z)=-e^{-i\vartheta}\frac{P(z)}{Q(z)}. \tag{3}$$

The zeros $z_j$ lie strictly between the adjacent zeros of $Q$, because $|s_j|<1/2$. On the unit circle away from its poles, $R$ is purely imaginary. This follows directly by expressing each factor $e^{ix}-e^{ix_j}$ as $2ie^{i(x+x_j)/2}\sin((x-x_j)/2)$ and using $Q(e^{ix})=2e^{imx/2}\cos(mx/2)$. Also

$$R(0)=e^{i\vartheta},\qquad |\vartheta|\le\pi\alpha<\pi/2. \tag{4}$$

Both $R$ and $1/R$ have positive real part in the disk. Here is a finite-dimensional proof, including the signs. For $s_j=0$, $R=(1-z^m)/(1+z^m)$, and its partial fraction representation is a sum of the positive-real kernels $(\eta+z)/(\eta-z)$ with coefficients $1/m$, at the zeros $\eta$ of $Q$. As the parameters change continuously along $\tau s_j$, $0\le\tau\le1$, the poles stay simple, the zeros stay strictly interlaced, and the coefficients of these kernels remain real and nonzero, since the boundary values are purely imaginary and no zero meets a pole. Their signs therefore remain positive. Subtracting all pole terms leaves a rational function without poles, hence a constant; its boundary real part is zero, so the constant is purely imaginary. The same argument applies to $1/R$, whose poles are the $z_j$. Thus, for some real $b$,

$$\frac1{R(z)}=ib+\sum_j\beta_j\frac{z_j+z}{z_j-z},\qquad \beta_j>0. \tag{5}$$

At $z=0$, (4) gives

$$\sum_j\beta_j=\cos\vartheta\le1. \tag{6}$$

Taking the magnitude of the residue at $z_j$ gives the exact identity

$$\beta_j=\frac{|Q(z_j)|}{2|P'(z_j)|}
       =\frac{\cos(\pi s_j)}{|P'(z_j)|}. \tag{7}$$

In particular,

$$\frac1{|P'(z_j)|}\le\frac{\beta_j}{\cos(\pi\alpha)}. \tag{8}$$

The real part of (5) is the exact Poisson representation

$$\operatorname{Re}\frac1{R(re^{ix})}
 =\sum_j\beta_j\frac{1-r^2}{|re^{ix}-z_j|^2}. \tag{9}$$

There are no zeros or poles of $R$ in the open disk, so every expression used here is defined.

## 3. A radial comparison with the exact exponent

Put $t_0=1/m$. For $t\ge t_0$, write $R_t(x)=R(e^{-t}e^{ix})$.

**Lemma 2.** Uniformly in all the parameters,

$$\frac{|R_t(x)|}{|R_T(x)|}\le C(T/t)^{2\alpha}
       \qquad(t_0\le t\le T\le1), \tag{10}$$

and

$$|R_t(x)|\le C t^{-2\alpha}\qquad(t_0\le t\le1). \tag{11}$$

**Proof.** Compare $P$ with $P_0$. The factors $P_0/Q$ at radii $e^{-t}$ with $mt\ge1$ have modulus between $\tanh(1/2)$ and $\coth(1/2)$. These bounds are absolute.

For a root at angle $\theta$,

$$\frac{\partial}{\partial\theta}\log|e^{-t}e^{ix}-e^{i\theta}|
 =-K_t(x-\theta),\qquad
 K_t(u)=\frac{\sin u}{2(\cosh t-\cos u)}. \tag{12}$$

Consequently the difference between the logarithmic perturbation products at heights $t$ and $T$ is bounded in absolute value by

$$\alpha h\sum_j\sup_{|v-a_j|\le h/2}|K_t(x-v)-K_T(x-v)|. \tag{13}$$

For an absolutely continuous periodic function $f$, the elementary cell estimate

$$h\sum_j\sup_{|v-a_j|\le h/2}|f(v)|
 \le\int_{-\pi}^{\pi}|f(v)|\,dv+h\int_{-\pi}^{\pi}|f'(v)|\,dv \tag{14}$$

follows by comparing a value in each cell to its average and integrating the derivative. For $0<t\le1$, direct differentiation of (12), or its single positive maximum on $(0,\pi)$, gives

$$\int_{-\pi}^{\pi}|K_t'(v)|\,dv\le C/t.$$

For $0<t\le T$, $K_t-K_T$ has the sign of $\sin u$, and direct integration gives

$$\int_{-\pi}^{\pi}|K_t-K_T|\,du
 =2\log\frac{\coth(t/2)}{\coth(T/2)}
 \le2\log(T/t). \tag{15}$$

The last inequality uses that $v\coth(v/2)$ is increasing. Since $h/t\le2\pi$, equations (13)–(15) yield $2\alpha\log(T/t)+C$ as an upper bound. This proves (10), after including the bounded unperturbed factors. Letting $T\to\infty$ in the same calculation gives $2\alpha\log\coth(t/2)+C\le2\alpha\log(C/t)+C$. At the origin $|R(0)|=1$, proving (11). The constant stays absolute because $2\alpha<1$. ∎

## 4. Proof of the full uniform Lebesgue estimate

The algebraic cardinal polynomial $P(z)/((z-z_j)P'(z_j))$ differs on the circle from $\ell_j$ only by a unimodular factor. For $|\zeta|=1$ and $0<r<1$,

$$|\zeta-z_l|^2\le r^{-1}|r\zeta-z_l|^2.$$

Applying this to the $m-1$ factors with $l\ne j$, with $r=e^{-t_0}$, gives

$$|\ell_j(x)|
 \le C\frac{|P(re^{ix})|}{|re^{ix}-z_j|\,|P'(z_j)|}
 \le\frac{C}{\cos(\pi\alpha)}
       |R_{t_0}(x)|\frac{\beta_j}{|re^{ix}-z_j|}. \tag{16}$$

Here $r^{-(m-1)/2}\le e^{1/2}$ and $|Q(re^{ix})|\le2$. This estimate includes evaluation exactly at a node; no division by a vanishing boundary factor occurs.

Divide the nodes into dyadic angular-distance annuli about $x$, starting at size $t_0$ and ending at size comparable to one; nodes at distance at least one form the last set. For an annulus of size $T$, $t_0\le T\le1$, its denominators in (16) are bounded below by $cT$, with the first annulus interpreted using the radial distance $t_0$. The Poisson kernel in (9), evaluated at radius $e^{-T}$, is at least $c/T$ on that annulus. Thus

$$\sum_{j\text{ in annulus}}\frac{\beta_j}{|re^{ix}-z_j|}
 \le C\operatorname{Re}\frac1{R_T(x)}
 \le \frac C{|R_T(x)|}. \tag{17}$$

Equations (10), (16), and (17) bound this annulus's contribution by

$$\frac{C}{\cos(\pi\alpha)}(T/t_0)^{2\alpha}. \tag{18}$$

The last set contributes at most $C|R_{t_0}(x)|/\cos(\pi\alpha)$ by (6), and (11) gives the same bound at the largest scale. Therefore

$$\sum_j|\ell_j(x)|\le
 \frac C{\cos(\pi\alpha)}\sum_{q=0}^{\lceil\log_2m\rceil}2^{2\alpha q}
 \le \frac C{\cos(\pi\alpha)}\frac{m^{2\alpha}-1}{\alpha}. \tag{19}$$

The final geometric-sum inequality is uniform for $0<\alpha<1/2$; use $2^{2\alpha}-1\ge2\alpha\log2$ and absorb the bounded factor from the last dyadic scale. Concavity of cosine on $[0,\pi/2]$ gives $\cos(\pi\alpha)\ge1-2\alpha$. Finally, $m=2N+1\le(5/2)N$ and $N\ge2$ imply

$$m^a-1\le C(N^a-1)\qquad(0<a\le1),$$

with absolute $C$, for example by integrating $a u^{a-1}$ and using $\log N\ge\log2$. Taking the supremum over $x$ proves (1).

## 5. A sector function for the regularized product

Only the second bound remains. Its constants may depend on fixed $\alpha>1/4$.

Let $s(\theta)=s_j$ on the cell $[a_j-h/2,a_j+h/2)$, periodically, and put

$$\phi(\theta)=\pi s(\theta),\qquad
 G(z)=\frac1{2\pi}\int_{-\pi}^{\pi}
       \phi(\theta)\frac{e^{i\theta}+z}{e^{i\theta}-z}\,d\theta,
 \qquad B(z)=e^{iG(z)}. \tag{20}$$

The real part of $G$ is the Poisson integral of $\phi$, so

$$|\operatorname{Re}G(z)|\le\pi\alpha. \tag{21}$$

Thus $B$ has an analytic logarithm with imaginary part in $[-\pi\alpha,\pi\alpha]$, and both $B^{1/(2\alpha)}$ and $B^{-1/(2\alpha)}$ have nonnegative real part.

**Lemma 3.** At $r=e^{-1/m}$, uniformly for all angles $x$,

$$C^{-1}|B(re^{ix})|\le|R(re^{ix})|\le C|B(re^{ix})|. \tag{22}$$

Moreover, if $|x-y|\le Ch$, with a fixed absolute multiple $C$, then

$$C_1^{-1}\le\frac{|B(re^{ix})|}{|B(re^{iy})|}\le C_1, \tag{23}$$

where $C_1$ depends only on that fixed multiple, and is independent of $m$, the shifts, and $0<\alpha<1/2$.

**Proof.** Let $f_z(\theta)=ze^{-i\theta}/(1-ze^{-i\theta})$. Choose all logarithms of $1-ze^{-i\theta}$ to vanish at $z=0$. Apart from a unimodular constant, the logarithm of $P/P_0$ is

$$L(z)=\sum_j\{\log(1-ze^{-i(a_j+s_jh)})-\log(1-ze^{-ia_j})\}.$$

Its linear term in the node shifts is $ih\sum_j s_j f_z(a_j)$. On the other hand,

$$G(z)-G(0)=\sum_j s_j\int_{a_j-h/2}^{a_j+h/2} f_z(\theta)\,d\theta.$$

Taylor's formula and cell quadrature therefore show

$$|L(z)-i(G(z)-G(0))|
 \le C h^2\sum_j\sup_{|v-a_j|\le h/2}|f_z'(v)|\le C
       \qquad(|z|=e^{-1/m}). \tag{24}$$

For clarity, the last bound follows from

$$|f_z'(v)|=\frac{|z|}{|1-ze^{-iv}|^2}
 \le \frac C{t_0^2+\operatorname{dist}(v,\arg z)^2},$$

whose cell suprema sum to at most $C(t_0^{-2}+(ht_0)^{-1})$; $h/t_0=2\pi$. The factors $\alpha$ and $\alpha^2$ from quadrature and Taylor are bounded absolutely. Since $G(0)$ is real and $P_0/Q$ is bounded above and below at this radius, (24) proves (22).

Differentiating the kernel in (20) gives

$$|\partial_xG(re^{ix})|\le C\alpha/t_0.$$

Integration over a distance $O(h)$ proves (23). The same derivative estimate applies if $\phi$ is restricted to any measurable arc. ∎

## 6. Local second moments of a sector function

Set

$$w_j=|B(re^{ia_j})|,\qquad r=e^{-1/m}.$$

**Lemma 4.** Fix $1/4<\alpha<1/2$. For every circular interval $I$ of $q$ consecutive grid indices, $1\le q\le m$, there is a positive number $b_I$ such that

$$\sum_{j\in I}w_j^2\le C_\alpha b_I^2q^{4\alpha},\qquad
 \sum_{j\in I}w_j^{-2}\le C_\alpha b_I^{-2}q^{4\alpha}. \tag{25}$$

**Proof.** We first specify the one standard harmonic-analysis estimate used here. If $f$ is analytic in a neighborhood of the closed disk and $\operatorname{Re}f\ge0$ in the disk, then

$$|\{\theta:|f(e^{i\theta})|>u\}|
       \le C|f(0)|/u. \tag{26}$$

Indeed, its real part has integral $2\pi\operatorname{Re}f(0)$, while the imaginary part minus $\operatorname{Im}f(0)$ is the periodic Hilbert transform of its real part. Markov's inequality, the weak $(1,1)$ inequality for that Hilbert transform, and a separate bound for the constant imaginary part give (26). The precise periodic weak theorem is Theorem 12.1 of Laugesen [4], applicable here to smooth, hence $L^2$, boundary data. Composition with a disk automorphism gives the corresponding harmonic-measure estimate with any interior point in place of zero.

Suppose first that $\ell=qh\le1/100$. Choose an arc $J$, centered at the middle of $I$, of length $8\ell$, and split $G=G_{\rm loc}+G_{\rm far}$ using $\phi\mathbf1_J$ and its complement in (20). On the arc containing $I$ and an extra cell on either side, at height $t_0$, the variation of $G_{\rm far}$ is at most $C\alpha$: the derivative of its kernel is bounded by $C/\operatorname{dist}^2$, whose integral outside $J$ is at most $C/\ell$, and the relevant angular variation is $O(\ell)$. Set

$$b_I=\exp(-\operatorname{Im}G_{\rm far}(re^{ix_I})),\qquad
 B_{\rm loc}=e^{iG_{\rm loc}},$$

where $x_I$ is the center angle. Thus $w_j/b_I$ and $|B_{\rm loc}(re^{ia_j})|$ are comparable by absolute factors, and the same holds for their reciprocals.

Put $p=1/(2\alpha)\in(1,2)$. Both functions

$$f_\pm(z)=\exp(\pm iG_{\rm loc}(z)/(2\alpha))$$

have nonnegative real part. Let $z_I=e^{-\ell}e^{ix_I}$. Since $\phi\mathbf1_J$ is supported on an arc of length $8\ell$ and the Herglotz kernel at $z_I$ has magnitude at most $C/\ell$ there,

$$|G_{\rm loc}(z_I)|\le C\alpha,\qquad |f_\pm(z_I)|\le C. \tag{27}$$

Apply (26) to $f_\pm(rz)$ after a disk automorphism sending zero to $e^{-(\ell-t_0)}e^{ix_I}$. This is legitimate because $\ell=qh\ge2\pi t_0>2t_0$. The resulting harmonic-measure density on the angular arc containing $I$ and its neighboring cells is bounded below by $c/\ell$. Consequently,

$$|\{x\text{ in that arc}:|B_{\rm loc}(re^{ix})|^{\pm1}>u\}|
       \le C\ell u^{-p}. \tag{28}$$

The derivative estimate in Lemma 3 shows that $|B_{\rm loc}|$ and its inverse vary by at most an absolute factor on each grid cell. Applying (28) to the disjoint cells around the selected grid points gives

$$\#\{j\in I:|B_{\rm loc}(re^{ia_j})|^{\pm1}>u\}
       \le Cq u^{-p}. \tag{29}$$

There is also the sharp pointwise cutoff

$$|B_{\rm loc}(re^{ix})|^{\pm1}\le Cq^{2\alpha} \tag{30}$$

on these cells. To verify its exponent, the imaginary part of the kernel in (20) is

$$\frac{\sin(x-\theta)}{\cosh t_0-\cos(x-\theta)}.$$

Since $|\phi|\le\pi\alpha$, integration of its absolute value over the support $J$, which lies within distance $C\ell$ of $x$, yields

$$|\operatorname{Im}G_{\rm loc}(re^{ix})|
 \le 2\alpha\log(\ell/t_0)+C\alpha.
$$

This follows by the elementary antiderivative $\log(\cosh t_0-\cos u)$ on each half-interval; $\ell/t_0=2\pi q$. It proves (30).

For either sign, integrate the counting function in (29), using (30) and the trivial count $q$ below level one:

$$\sum_{j\in I}|B_{\rm loc}(re^{ia_j})|^{\pm2}
 \le Cq+Cq\int_1^{Cq^{2\alpha}}u^{1-p}\,du
 \le C_\alpha q^{4\alpha}. \tag{31}$$

Here $2-p>0$ is precisely the strict assumption $\alpha>1/4$. Restoring $b_I$ proves (25) for small arcs.

If $qh>1/100$, use the whole circle as the local region and take $b_I=1$. Now $G(0)$ is real, so $|\exp(\pm iG(0)/(2\alpha))|=1$. Apply (26) directly to $\exp(\pm iG(rz)/(2\alpha))$, use cell comparability, and integrate the full-circle kernel to get the cutoff $Cm^{2\alpha}$. The same calculation proves the bounds with $m^{4\alpha}$. Since $m\le Cq$ in this case and $4\alpha<2$, these imply (25), with absolute comparison factors. ∎

## 7. Cardinal matrix and the no-logarithm spectral estimate

Let $E$ be the interpolation matrix from the perturbed nodes to the equispaced nodes:

$$E_{kj}=\ell_j(a_k).$$

If $F_0=m^{-1/2}[e^{i\nu a_k}]$ is the unitary Fourier matrix, then

$$E=F_0F^{-1},\qquad \|E\|_2=\Gamma_N. \tag{32}$$

We claim the pointwise bound

$$|E_{kj}|\le C_\alpha\frac{w_k/w_j}{1+d(k,j)},\qquad
 d(k,j)=\min_{v\in\mathbb Z}|k-j+vm|. \tag{33}$$

To prove it, (9) at $rz_j$ gives

$$\beta_j\frac{1+r}{1-r}\le\operatorname{Re}\frac1{R(rz_j)}
 \le\frac1{|R(rz_j)|},$$

so $\beta_j\le C m^{-1}|R(rz_j)|^{-1}$. By (7), (22), and (23),

$$\frac1{|P'(z_j)|}\le C_\alpha m^{-1}w_j^{-1}.$$

The product inequality preceding (16) gives

$$|E_{kj}|\le C\frac{|P(re^{ia_k})|}{|re^{ia_k}-z_j|\,|P'(z_j)|}.$$

Lemma 3 and the bounded $Q$ factor bound the numerator by $Cw_k$. Finally,

$$|re^{ia_k}-z_j|\ge c\frac{1+d(k,j)}m,$$

because $t_0=1/m$ handles $d=0$, and for $d\ge1$ the angular distance is at least $(d-\alpha)h\ge dh/2$. This proves (33).

Decompose $E$ according to the dyadic distance ranges $d<2$, and $R\le d<2R$ with $R=2,4,8,\ldots$, up to the circle's diameter. At a fixed scale $R$, partition the cyclic indices into consecutive blocks of length at most $R$. Each block interacts in this distance range with only an absolute number of other blocks. The union of two interacting blocks lies in a circular interval containing at most $CR$ indices, or is covered by the whole circle when $R$ is comparable to $m$.

For an interacting row block $I_1$ and column block $I_2$, (33) and Cauchy–Schwarz give the following norm bound for the block, including any mask selecting the distance range:

$$\|E^{(R)}_{I_1,I_2}\|_2
 \le\frac{C_\alpha}{R}
       \Big(\sum_{k\in I_1}w_k^2\Big)^{1/2}
       \Big(\sum_{j\in I_2}w_j^{-2}\Big)^{1/2}
 \le C_\alpha R^{4\alpha-1}. \tag{34}$$

The last step applies Lemma 4 to one interval containing both blocks, so its two normalization factors cancel. The same estimate, with a constant, handles $d<2$. A block matrix with uniformly bounded numbers of nonzero blocks in every block row and column has norm at most an absolute multiple of its largest block norm: apply the scalar row/column bound to the matrix of block norms. Hence (34) gives

$$\|E^{(R)}\|_2\le C_\alpha R^{4\alpha-1}.$$

Since $4\alpha-1>0$, summing the dyadic scales is a geometric sum:

$$\Gamma_N=\|E\|_2
 \le C_\alpha\sum_{R\text{ dyadic},\ R\le m}R^{4\alpha-1}
 \le C_\alpha m^{4\alpha-1}
 \le C_\alpha N^{4\alpha-1}. \tag{35}$$

This proves (2). Together with Section 4 it proves Theorem 1 for the full original bundled target. No assertion at $\alpha=1/4$ is made; at that endpoint the second-moment integral in (31) and the scale summation require different estimates.

## 8. Attribution, scope, and verification

The two exact targets originate in Austin and Trefethen [1] and Austin's thesis [2]. Chen, Lin, and Zhang [3] prove the second bound with an additional logarithm; the present argument removes it. The only imported analytic inequality beyond elementary complex analysis is the periodic Hilbert transform's weak $(1,1)$ estimate, in Laugesen [4], Theorem 12.1, printed p.67. Its applicability to the smooth boundary data used in Lemma 4 is explained there. All grid-product, residue, localization, and matrix estimates needed for this conclusion appear in Sections 1–7.

Nodes index the rows of the normalized Fourier matrix in this proof, exactly as in the canonical statement. A convention with frequency indices as rows transposes this matrix and preserves all singular values, including the inverse norm. The identity $E=F_0F^{-1}$ in (32) uses the displayed row convention.

The first estimate has one absolute constant simultaneously for all $0<\alpha<1/2$. The second constant may depend on a fixed $1/4<\alpha<1/2$. No estimate at $\alpha=1/4$, no assertion about optimal constants, and no rectangular oversampling or restricted-isometry statement is made.

The original frozen source, dated public eligibility check, numerical identity checks, and review reports are retained in the [submission record](../../references/stepaniants-ie26-2026-09-12/README.md). The diagnostics test three deterministic instances and do not establish any quantified theorem. The mathematical proof is independent of those tests. Source and eligibility checks are bounded; no priority claim is made.

## References

1. A. P. Austin and L. N. Trefethen, *Trigonometric interpolation and quadrature in perturbed points*, SIAM J. Numer. Anal. 55 (2017), 2113–2122. The conjectured replacement in equation (12), pp.2115–2116, and the second-norm conjecture, p.2119. [DOI](https://doi.org/10.1137/16M1107760); [author PDF](https://people.maths.ox.ac.uk/trefethen/perturbed.pdf).
2. A. P. Austin, *Some New Results on and Applications of Interpolation in Numerical Computation*, D.Phil. thesis, University of Oxford, 2016. Conjectures 3.5 and 3.10, printed pp.75 and 82. [Author PDF](https://personal.math.vt.edu/apaustin/pubs/DPhilThesis.pdf). The endpoint assertion of the thesis is not imported into (2).
3. L. Chen, R. Lin, and H. Zhang, *The smallest singular value of nonuniform Fourier matrices*, arXiv:2608.21960v1, 22 August 2026. Theorems 1.4–1.5 and Section 3. [Versioned record](https://arxiv.org/abs/2608.21960v1); [full text](https://arxiv.org/html/2608.21960v1).
4. R. S. Laugesen, *Harmonic Analysis Lecture Notes*, arXiv:0903.3845v2, 17 May 2017, Theorem 12.1, printed p.67. [Versioned record](https://arxiv.org/abs/0903.3845v2); [PDF](https://arxiv.org/pdf/0903.3845v2).
